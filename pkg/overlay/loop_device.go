//go:build linux
// +build linux

package overlay

import (
	"fmt"
	"os"
	"strings"
	"syscall"
	"time"
	"unsafe"
)

const (
	LOOP_SET_FD       = 0x4C00
	LOOP_CLR_FD       = 0x4C01
	LOOP_SET_STATUS64 = 0x4C04
	LOOP_GET_STATUS64 = 0x4C05
	LOOP_CTL_GET_FREE = 0x4C82
	BLKGETSIZE64      = 0x80081272 // Get device size in bytes

	LO_NAME_SIZE       = 64
	LO_CRYPT_NAME_SIZE = 64
	LO_KEY_SIZE        = 32

	// Enable discard (TRIM) on loop device to speed mounts in sparse images
	LO_FLAGS_DISCARD = 8
	// Read-only flag for loop device
	LO_FLAGS_READ_ONLY = 1
)

type loopInfo64 struct {
	Device         uint64
	Inode          uint64
	Rdevice        uint64
	Rinode         uint64
	Offset         uint64
	Sizelimit      uint64
	Number         uint32
	EncryptType    uint32
	EncryptKeySize uint32
	Flags          uint32
	FileName       [LO_NAME_SIZE]byte
	CryptName      [LO_CRYPT_NAME_SIZE]byte
	EncryptKey     [LO_KEY_SIZE]byte
	_              [16]byte // lo_init[2] or padding
}

func ioctl(fd int, req uintptr, arg uintptr) error {
	_, _, errno := syscall.Syscall(syscall.SYS_IOCTL, uintptr(fd), req, arg)
	if errno != 0 {
		return errno
	}
	return nil
}

// attachLoopDevice attaches a backing file to a loop device with discard support
// Returns the loop device path (e.g., /dev/loop0) or an error
func attachLoopDevice(backingFile string) (string, error) {
	return attachLoopDeviceWithFlags(backingFile, false)
}

// attachLoopDeviceReadonly attaches a backing file to a loop device in readonly mode
// Returns the loop device path (e.g., /dev/loop0) or an error
func attachLoopDeviceReadonly(backingFile string) (string, error) {
	return attachLoopDeviceWithFlags(backingFile, true)
}

// attachLoopDeviceWithFlags attaches a backing file to a loop device with specified flags
// Returns the loop device path (e.g., /dev/loop0) or an error
func attachLoopDeviceWithFlags(backingFile string, readonly bool) (string, error) {
	// Open loop-control device
	ctl, err := os.OpenFile("/dev/loop-control", os.O_RDWR, 0)
	if err != nil {
		return "", fmt.Errorf("failed to open loop-control: %w", err)
	}
	defer ctl.Close()

	// Acquire exclusive flock on loop-control to make get-free + attach atomic
	// This prevents race conditions when multiple processes try to get a free loop
	// device number concurrently - they could get the same number before either
	// has attached to it
	if err := syscall.Flock(int(ctl.Fd()), syscall.LOCK_EX); err != nil {
		return "", fmt.Errorf("failed to acquire loop-control lock: %w", err)
	}
	// Lock is automatically released when ctl is closed via defer

	// Get free loop number
	// Note: LOOP_CTL_GET_FREE returns the number in the syscall return value
	ret, _, errno := syscall.Syscall(syscall.SYS_IOCTL, ctl.Fd(), LOOP_CTL_GET_FREE, 0)
	if errno != 0 {
		return "", fmt.Errorf("LOOP_CTL_GET_FREE failed: %w", errno)
	}
	loopNum := int(ret)

	loopPath := fmt.Sprintf("/dev/loop%d", loopNum)

	// Create the loop device file if it doesn't exist
	if _, err := os.Stat(loopPath); os.IsNotExist(err) {
		// Create the loop device with major 7, minor = loopNum
		// Device number = (major << 8) | minor
		dev := (7 << 8) | loopNum
		if err := syscall.Mknod(loopPath, syscall.S_IFBLK|0660, dev); err != nil {
			return "", fmt.Errorf("failed to create loop device %s: %w", loopPath, err)
		}
	}

	loop, err := os.OpenFile(loopPath, os.O_RDWR, 0)
	if err != nil {
		return "", fmt.Errorf("failed to open loop device %s: %w", loopPath, err)
	}
	defer loop.Close()

	// Open backing file with appropriate flags
	fileFlags := os.O_RDWR
	if readonly {
		fileFlags = os.O_RDONLY
	}
	f, err := os.OpenFile(backingFile, fileFlags, 0)
	if err != nil {
		return "", fmt.Errorf("failed to open backing file %s: %w", backingFile, err)
	}
	defer f.Close()

	// Attach file to loop
	if err := ioctl(int(loop.Fd()), LOOP_SET_FD, uintptr(f.Fd())); err != nil {
		return "", fmt.Errorf("LOOP_SET_FD failed: %w", err)
	}

	// Prepare loop_info64 with appropriate flags
	var info loopInfo64
	info.Flags = LO_FLAGS_DISCARD
	if readonly {
		info.Flags |= LO_FLAGS_READ_ONLY
	}
	copy(info.FileName[:], backingFile)

	// Set status (LOOP_SET_STATUS64)
	if err := ioctl(int(loop.Fd()), LOOP_SET_STATUS64, uintptr(unsafe.Pointer(&info))); err != nil {
		// Cleanup: clear fd
		_ = ioctl(int(loop.Fd()), LOOP_CLR_FD, 0)
		return "", fmt.Errorf("LOOP_SET_STATUS64 failed: %w", err)
	}

	return loopPath, nil
}

// detachLoopDevice detaches a loop device and waits for kernel to release it
func detachLoopDevice(loopPath string) error {
	// Extract loop number from path (e.g., /dev/loop0 -> loop0)
	loopName := loopPath
	if idx := strings.LastIndex(loopPath, "/"); idx >= 0 {
		loopName = loopPath[idx+1:]
	}

	// Check sysfs holders directory to see what's using this loop device
	holdersPath := fmt.Sprintf("/sys/block/%s/holders", loopName)

	// Wait for any holders to release the device before detaching
	// This is more reliable than polling the device status
	maxWaitBeforeDetach := 100 // 100 iterations × 10ms = 1 second
	for i := 0; i < maxWaitBeforeDetach; i++ {
		entries, err := os.ReadDir(holdersPath)
		if err != nil {
			// If sysfs is unavailable, fall back to immediate detach attempt
			break
		}
		if len(entries) == 0 {
			// No holders, safe to proceed with detach
			break
		}
		// Still has holders, wait a bit
		time.Sleep(10 * time.Millisecond)
	}

	loop, err := os.OpenFile(loopPath, os.O_RDWR, 0)
	if err != nil {
		// If device doesn't exist, treat as already detached (success)
		if os.IsNotExist(err) {
			return nil
		}
		return fmt.Errorf("failed to open loop device %s: %w", loopPath, err)
	}
	defer loop.Close()

	if err := ioctl(int(loop.Fd()), LOOP_CLR_FD, 0); err != nil {
		return fmt.Errorf("LOOP_CLR_FD failed: %w", err)
	}

	// Verify the loop device is actually detached
	// After LOOP_CLR_FD succeeds, the kernel should release it quickly,
	// but we still verify to catch any edge cases. Give it up to 1 second.
	for i := 0; i < 100; i++ {
		// Check via ioctl - if it fails with ENXIO, device is detached
		if err := ioctl(int(loop.Fd()), LOOP_GET_STATUS64, 0); err != nil {
			// Error means device is not configured (detached) - success!
			return nil
		}
		// Also check sysfs holders
		if entries, err := os.ReadDir(holdersPath); err == nil && len(entries) == 0 {
			// No holders in sysfs, device is released
			return nil
		}
		// Still attached, wait a bit
		time.Sleep(10 * time.Millisecond)
	}

	return fmt.Errorf("loop device %s still attached after detach command", loopPath)
}

//go:build linux
// +build linux

package overlay

import (
	"fmt"
	"os"
	"syscall"
	"unsafe"
)

const (
	LOOP_SET_FD       = 0x4C00
	LOOP_CLR_FD       = 0x4C01
	LOOP_SET_STATUS64 = 0x4C04
	LOOP_CTL_GET_FREE = 0x4C82

	LO_NAME_SIZE       = 64
	LO_CRYPT_NAME_SIZE = 64
	LO_KEY_SIZE        = 32

	// Enable discard (TRIM) on loop device to speed mounts in sparse images
	LO_FLAGS_DISCARD = 8
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
	ctl, err := os.OpenFile("/dev/loop-control", os.O_RDWR, 0)
	if err != nil {
		return "", fmt.Errorf("failed to open loop-control: %w", err)
	}
	defer ctl.Close()

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

	f, err := os.OpenFile(backingFile, os.O_RDWR, 0)
	if err != nil {
		return "", fmt.Errorf("failed to open backing file %s: %w", backingFile, err)
	}
	defer f.Close()

	// Attach file to loop
	if err := ioctl(int(loop.Fd()), LOOP_SET_FD, uintptr(f.Fd())); err != nil {
		return "", fmt.Errorf("LOOP_SET_FD failed: %w", err)
	}

	// Prepare loop_info64 with discard flag
	var info loopInfo64
	info.Flags = LO_FLAGS_DISCARD
	copy(info.FileName[:], backingFile)

	// Set status (LOOP_SET_STATUS64)
	if err := ioctl(int(loop.Fd()), LOOP_SET_STATUS64, uintptr(unsafe.Pointer(&info))); err != nil {
		// Cleanup: clear fd
		_ = ioctl(int(loop.Fd()), LOOP_CLR_FD, 0)
		return "", fmt.Errorf("LOOP_SET_STATUS64 failed: %w", err)
	}

	return loopPath, nil
}

// detachLoopDevice detaches a loop device
func detachLoopDevice(loopPath string) error {
	loop, err := os.OpenFile(loopPath, os.O_RDWR, 0)
	if err != nil {
		return fmt.Errorf("failed to open loop device %s: %w", loopPath, err)
	}
	defer loop.Close()

	if err := ioctl(int(loop.Fd()), LOOP_CLR_FD, 0); err != nil {
		return fmt.Errorf("LOOP_CLR_FD failed: %w", err)
	}

	return nil
}

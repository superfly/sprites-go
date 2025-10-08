//go:build linux

package overlay

import (
	"fmt"

	"golang.org/x/sys/unix"
)

const (
	// tmpfs filesystem magic number
	tmpfsMagic = 0x01021994
	// overlayfs filesystem magic number
	overlayFSMagic = 0x794c7630
	// ext4 filesystem magic number
	ext4Magic = 0xEF53
)

// mountTmpfsShared mounts a tmpfs filesystem at the specified path with shared propagation
func mountTmpfsShared(target string) error {
	// First mount as tmpfs
	if err := unix.Mount("tmpfs", target, "tmpfs", 0, ""); err != nil {
		return err
	}
	// Then make it shared - this requires a separate mount syscall
	return unix.Mount("", target, "", unix.MS_SHARED, "")
}

// mountOverlayFS mounts an overlay filesystem using syscall
func mountOverlayFS(target, lowerdir, upperdir, workdir string) error {
	// Build mount options string
	// Format: lowerdir=/path,upperdir=/path,workdir=/path
	options := fmt.Sprintf("lowerdir=%s,upperdir=%s,workdir=%s", lowerdir, upperdir, workdir)

	// Mount overlay filesystem
	// source: "overlay" (the filesystem name)
	// target: the mount point
	// fstype: "overlay"
	// flags: 0 (no special flags)
	// data: the options string
	return unix.Mount("overlay", target, "overlay", 0, options)
}

// mountBind creates a bind mount from source to target
func mountBind(source, target string) error {
	return unix.Mount(source, target, "", unix.MS_BIND, "")
}

// remountReadonly remounts a filesystem as readonly
func remountReadonly(target string) error {
	// MS_REMOUNT|MS_RDONLY|MS_BIND for remounting bind mounts as readonly
	return unix.Mount("", target, "", unix.MS_REMOUNT|unix.MS_RDONLY|unix.MS_BIND, "")
}

// mountExt4 mounts an ext4 filesystem with options
func mountExt4(device, target, options string) error {
	return unix.Mount(device, target, "ext4", 0, options)
}

// unmount unmounts a filesystem at the specified path
func unmount(target string) error {
	return unix.Unmount(target, 0)
}

// isMounted checks if a path is a mount point by comparing device ID with parent
func isMounted(path string) (bool, error) {
	var stat, parentStat unix.Stat_t

	if err := unix.Stat(path, &stat); err != nil {
		return false, err
	}

	parent := path + "/.."
	if err := unix.Stat(parent, &parentStat); err != nil {
		return false, err
	}

	// If dev IDs differ, it's a mount point
	return stat.Dev != parentStat.Dev, nil
}

// isTmpfsMounted checks if the path is mounted as tmpfs
func isTmpfsMounted(path string) (bool, error) {
	var stat unix.Statfs_t
	if err := unix.Statfs(path, &stat); err != nil {
		return false, err
	}
	return stat.Type == tmpfsMagic, nil
}

// isOverlayFSMounted checks if the path is mounted as overlayfs
func isOverlayFSMounted(path string) (bool, error) {
	var stat unix.Statfs_t
	if err := unix.Statfs(path, &stat); err != nil {
		return false, err
	}
	return stat.Type == overlayFSMagic, nil
}

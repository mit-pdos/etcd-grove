package driver

import (
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
)

// A disk is one replica's machine's disk, for power losses: an ext4 filesystem (configuration C
// of the Linux file extension, notes/axiom-review/fs-config/README.md: mkfs.ext4's defaults on a
// 1 GiB sparse image, mounted with the default options) on a dm-flakey device over a loop device,
// so that a power loss can be made the way xfstests makes one (_flakey_drop_and_remount): the
// device is switched to drop every write without flushing anything (dmsetup suspend --nolockfs),
// the filesystem unmounted (the page cache's dirty pages and the journal's last commits go to the
// device, which drops them), the device switched back, and the filesystem mounted again (the
// journal replayed, as at boot). What survives is what reached the device before the switch:
// everything fsync made durable, and whatever writeback happened to write on its own.
//
// It needs root (sudo without a password): losetup, dmsetup, mkfs.ext4, mount.
type disk struct {
	img     string // the image file
	loop    string // its loop device
	name    string // the dm device's name (/dev/mapper/<name>)
	mnt     string // where the filesystem is mounted
	sectors string // the device's size, in 512-byte sectors
}

// sudo runs a command as root; its error carries the command's output.
func sudo(args ...string) (string, error) {
	out, err := exec.Command("sudo", append([]string{"-n"}, args...)...).CombinedOutput()
	if err != nil {
		return "", fmt.Errorf("sudo %s: %v: %s", strings.Join(args, " "), err, strings.TrimSpace(string(out)))
	}
	return strings.TrimSpace(string(out)), nil
}

// sudoIn runs a command as root with stdin.
func sudoIn(stdin string, args ...string) error {
	cmd := exec.Command("sudo", append([]string{"-n"}, args...)...)
	cmd.Stdin = strings.NewReader(stdin)
	if out, err := cmd.CombinedOutput(); err != nil {
		return fmt.Errorf("sudo %s: %v: %s", strings.Join(args, " "), err, strings.TrimSpace(string(out)))
	}
	return nil
}

// PowerAvailable says whether this process can make disks: sudo without a password, and the
// dm-flakey target (loaded if it is a module).
func PowerAvailable() error {
	if _, err := sudo("true"); err != nil {
		return err
	}
	sudo("modprobe", "dm-flakey")
	out, err := sudo("dmsetup", "targets")
	if err != nil {
		return err
	}
	if !strings.Contains(out, "flakey") {
		return fmt.Errorf("no dm-flakey target")
	}
	return nil
}

// tables are the dm-flakey tables: writes pass (up for 180s, then down 0s: always up), and
// writes dropped (up 0s, down 180s, dropping writes while down: always dropping). Reads pass in
// both.
func (d *disk) allowTable() string {
	return fmt.Sprintf("0 %s flakey %s 0 180 0\n", d.sectors, d.loop)
}

func (d *disk) dropTable() string {
	return fmt.Sprintf("0 %s flakey %s 0 0 180 1 drop_writes\n", d.sectors, d.loop)
}

// newDisk makes a disk in the directory work, named name (unique on the machine: the dm
// device's name), and mounts it at work/name.
func newDisk(work, name string) (*disk, error) {
	d := &disk{img: filepath.Join(work, name+".img"), name: name, mnt: filepath.Join(work, name)}
	if err := os.MkdirAll(d.mnt, 0o755); err != nil {
		return nil, err
	}
	f, err := os.Create(d.img)
	if err != nil {
		return nil, err
	}
	err = f.Truncate(1 << 30)
	f.Close()
	if err != nil {
		return nil, err
	}
	if d.loop, err = sudo("losetup", "--find", "--show", d.img); err != nil {
		return nil, err
	}
	if d.sectors, err = sudo("blockdev", "--getsz", d.loop); err != nil {
		d.destroy()
		return nil, err
	}
	if err := sudoIn(d.allowTable(), "dmsetup", "create", d.name); err != nil {
		d.name = ""
		d.destroy()
		return nil, err
	}
	if _, err := sudo("mkfs.ext4", "-q", "-F", d.dev()); err != nil {
		d.destroy()
		return nil, err
	}
	if err := d.mount(); err != nil {
		d.destroy()
		return nil, err
	}
	if _, err := sudo("chmod", "777", d.mnt); err != nil {
		d.destroy()
		return nil, err
	}
	// the mode made durable, so that a power loss does not take it away
	if _, err := sudo("sync", "-f", d.mnt); err != nil {
		d.destroy()
		return nil, err
	}
	return d, nil
}

// dev is the dm device's path.
func (d *disk) dev() string { return "/dev/mapper/" + d.name }

// mount mounts the filesystem with ext4's default options.
func (d *disk) mount() error {
	_, err := sudo("mount", "-t", "ext4", d.dev(), d.mnt)
	return err
}

// swap replaces the dm device's table by table without flushing anything (--nolockfs: the
// filesystem is not frozen, so its dirty pages are not written first).
func (d *disk) swap(table string) error {
	if _, err := sudo("dmsetup", "suspend", "--nolockfs", d.name); err != nil {
		return err
	}
	if err := sudoIn(table, "dmsetup", "load", d.name); err != nil {
		sudo("dmsetup", "resume", d.name)
		return err
	}
	_, err := sudo("dmsetup", "resume", d.name)
	return err
}

// powerLoss makes the disk lose power: everything not yet on the device is lost; the filesystem
// is then mounted again, recovered as at boot. Every process using the filesystem must have
// exited.
func (d *disk) powerLoss() error {
	if err := d.swap(d.dropTable()); err != nil {
		return err
	}
	if _, err := sudo("umount", d.mnt); err != nil {
		return err
	}
	if err := d.swap(d.allowTable()); err != nil {
		return err
	}
	return d.mount()
}

// destroy unmounts the filesystem and removes the devices and the image, as far as they exist.
func (d *disk) destroy() {
	sudo("umount", d.mnt)
	if d.name != "" {
		sudo("dmsetup", "remove", "--retry", d.name)
	}
	if d.loop != "" {
		sudo("losetup", "-d", d.loop)
	}
	os.Remove(d.img)
	os.Remove(d.mnt)
}

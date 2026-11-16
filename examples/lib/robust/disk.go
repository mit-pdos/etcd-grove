package robust

import (
	"fmt"
	"os"
	"path/filepath"
	"strings"
)

// A Disk is one machine's disk, for power losses: an ext4 filesystem (configuration C of the
// Linux file extension, notes/axiom-review/fs-config/README.md: mkfs.ext4's defaults on a 1 GiB
// sparse image, mounted with the default options) on a dm-flakey device over a loop device, so
// that a power loss can be made the way xfstests makes one (_flakey_drop_and_remount): the device
// is switched to drop every write without flushing anything (dmsetup suspend --nolockfs), the
// filesystem unmounted (the page cache's dirty pages and the journal's last commits go to the
// device, which drops them), the device switched back, and the filesystem mounted again (the
// journal replayed, as at boot). What survives is what reached the device before the switch:
// everything fsync made durable, and whatever writeback happened to write on its own.
//
// It needs root (or sudo without a password): losetup, dmsetup, mkfs.ext4, mount.
type Disk struct {
	Mnt     string // where the filesystem is mounted
	img     string // the image file
	loop    string // its loop device
	name    string // the dm device's name (/dev/mapper/<name>)
	sectors string // the device's size, in 512-byte sectors
}

// PowerAvailable says whether this process can make disks: root or sudo without a password, and
// the dm-flakey target (loaded if it is a module).
func PowerAvailable() error {
	if _, err := asRoot("true"); err != nil {
		return err
	}
	asRoot("modprobe", "dm-flakey")
	out, err := asRoot("dmsetup", "targets")
	if err != nil {
		return err
	}
	if !strings.Contains(out, "flakey") {
		return fmt.Errorf("no dm-flakey target")
	}
	return nil
}

// allowTable is the dm-flakey table that passes writes (up for 180s, then down 0s: always up);
// dropTable drops them (up 0s, down 180s, dropping writes while down: always dropping). Reads
// pass in both.
func (d *Disk) allowTable() string {
	return fmt.Sprintf("0 %s flakey %s 0 180 0\n", d.sectors, d.loop)
}

func (d *Disk) dropTable() string {
	return fmt.Sprintf("0 %s flakey %s 0 0 180 1 drop_writes\n", d.sectors, d.loop)
}

// NewDisk makes a disk in the directory work, named name (unique on the machine: the dm
// device's name), and mounts it at work/name, writable by everyone.
func NewDisk(work, name string) (*Disk, error) {
	d := &Disk{img: filepath.Join(work, name+".img"), name: name, Mnt: filepath.Join(work, name)}
	if err := os.MkdirAll(d.Mnt, 0o755); err != nil {
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
	if d.loop, err = asRoot("losetup", "--find", "--show", d.img); err != nil {
		return nil, err
	}
	if d.sectors, err = asRoot("blockdev", "--getsz", d.loop); err != nil {
		d.Destroy()
		return nil, err
	}
	if err := asRootIn(d.allowTable(), "dmsetup", "create", d.name); err != nil {
		d.name = ""
		d.Destroy()
		return nil, err
	}
	if _, err := asRoot("mkfs.ext4", "-q", "-F", d.dev()); err != nil {
		d.Destroy()
		return nil, err
	}
	if err := d.mount(); err != nil {
		d.Destroy()
		return nil, err
	}
	if _, err := asRoot("chmod", "777", d.Mnt); err != nil {
		d.Destroy()
		return nil, err
	}
	// the mode made durable, so that a power loss does not take it away
	if _, err := asRoot("sync", "-f", d.Mnt); err != nil {
		d.Destroy()
		return nil, err
	}
	return d, nil
}

// dev is the dm device's path.
func (d *Disk) dev() string { return "/dev/mapper/" + d.name }

// mount mounts the filesystem with ext4's default options.
func (d *Disk) mount() error {
	_, err := asRoot("mount", "-t", "ext4", d.dev(), d.Mnt)
	return err
}

// swap replaces the dm device's table by table without flushing anything (--nolockfs: the
// filesystem is not frozen, so its dirty pages are not written first).
func (d *Disk) swap(table string) error {
	if _, err := asRoot("dmsetup", "suspend", "--nolockfs", d.name); err != nil {
		return err
	}
	if err := asRootIn(table, "dmsetup", "load", d.name); err != nil {
		asRoot("dmsetup", "resume", d.name)
		return err
	}
	_, err := asRoot("dmsetup", "resume", d.name)
	return err
}

// PowerLoss makes the disk lose power: everything not yet on the device is lost; the filesystem
// is then mounted again, recovered as at boot. Every process using the filesystem must have
// exited.
func (d *Disk) PowerLoss() error {
	if err := d.swap(d.dropTable()); err != nil {
		return err
	}
	if _, err := asRoot("umount", d.Mnt); err != nil {
		return err
	}
	if err := d.swap(d.allowTable()); err != nil {
		return err
	}
	return d.mount()
}

// Destroy unmounts the filesystem and removes the devices and the image, as far as they exist.
func (d *Disk) Destroy() {
	asRoot("umount", d.Mnt)
	if d.name != "" {
		asRoot("dmsetup", "remove", "--retry", d.name)
	}
	if d.loop != "" {
		asRoot("losetup", "-d", d.loop)
	}
	os.Remove(d.img)
	os.Remove(d.Mnt)
}

// SyncFS makes durable everything of dir's filesystem (syncfs(2), by sync -f): what a supervisor
// does before restarting a killed process, after which the restart is the one the Linux file
// extension allows (its "Restarts" assumption, GooseLang/Ext/Fs/Impl.lean).
func SyncFS(dir string) error {
	if _, err := run("sync", "-f", dir); err != nil {
		return err
	}
	return nil
}

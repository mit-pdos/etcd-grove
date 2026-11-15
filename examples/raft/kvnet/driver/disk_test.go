package driver

import (
	"os"
	"path/filepath"
	"testing"

	"github.com/mit-pdos/etcd-grove/examples/lib/durable"
)

// TestPowerLoss checks the disks' power loss: a file written and synced survives it, as does one
// written by durable.Write; a file written without a sync, and a rename not synced, do not.
// It needs sudo without a password (skipped otherwise).
func TestPowerLoss(t *testing.T) {
	if err := PowerAvailable(); err != nil {
		t.Skip("power losses unavailable:", err)
	}
	d, err := newDisk(t.TempDir(), "kvnet-disktest")
	if err != nil {
		t.Fatal(err)
	}
	defer d.destroy()
	synced := filepath.Join(d.mnt, "synced")
	f, err := os.Create(synced)
	if err != nil {
		t.Fatal(err)
	}
	f.WriteString("synced")
	f.Sync()
	f.Close()
	if err := syncfs(d.mnt); err != nil { // the directory entry
		t.Fatal(err)
	}
	durable.Write(filepath.Join(d.mnt, "durable"), "durable")
	if err := os.WriteFile(filepath.Join(d.mnt, "unsynced"), []byte("unsynced"), 0o644); err != nil {
		t.Fatal(err)
	}
	if err := os.WriteFile(synced, []byte("overwritten"), 0o644); err != nil {
		t.Fatal(err)
	}
	if err := d.powerLoss(); err != nil {
		t.Fatal(err)
	}
	if b, err := os.ReadFile(synced); err != nil || string(b) != "synced" {
		t.Errorf("the synced file after the power loss: %q, %v (want \"synced\": its overwrite was never synced)", b, err)
	}
	if b, err := os.ReadFile(filepath.Join(d.mnt, "durable")); err != nil || string(b) != "durable" {
		t.Errorf("durable.Write's file after the power loss: %q, %v", b, err)
	}
	if _, err := os.Stat(filepath.Join(d.mnt, "unsynced")); !os.IsNotExist(err) {
		t.Errorf("the unsynced file survived the power loss: %v", err)
	}
}

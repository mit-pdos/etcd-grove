// fs-link: the metadata calls of etcd's snap.SaveDBFrom (server/etcdserver/api/snap/db.go,
// fork 30df685e4), run on a filesystem of configuration C under dm-log-writes (link.sh), so that
// lreplay.py can rebuild the disk at every flush/FUA point and check each crash image against the
// assumptions of the SaveDBFrom axiom (examples/osfs/semantics/meta_link_*.go). Each call is
// printed as "OP name begin_ns end_ns err"; a dm-log-writes mark follows each returned call.
//
// Usage: linkops ROOT SCENARIO [SLEEP_MS]
//
//	snapsave        SaveDBFrom of index 5 into an empty directory: create tmp1; write 64 KiB;
//	                fsync; close; link tmp1 0000000000000005.snap.db; unlink tmp1; fsync ROOT
//	snapsave-exist  the same with 0000000000000005.snap.db already there (synced, "old"):
//	                the link fails with EEXIST; unlink tmp1; fsync ROOT
//
// SLEEP_MS between the calls (default 1200, with commit=1: each call's transaction commits on its
// own, so the replay sees every prefix).
package main

import (
	"bytes"
	"errors"
	"fmt"
	"os"
	"os/exec"
	"strconv"
	"time"
)

var t0 = time.Now()

func now() int64 { return time.Since(t0).Nanoseconds() }

// op runs one call, prints it, and marks the log after it returned. want: the error expected
// (nil, or os.ErrExist for the kept file's link).
func op(name string, want error, f func() error) {
	b := now()
	err := f()
	e := now()
	fmt.Printf("OP %s %d %d %v\n", name, b, e, err)
	if (want == nil && err != nil) || (want != nil && !errors.Is(err, want)) {
		panic(fmt.Sprintf("%s: %v, want %v", name, err, want))
	}
	if lw := os.Getenv("LWMARK"); lw != "" {
		if err := exec.Command("dmsetup", "message", lw, "0", "mark", name).Run(); err != nil {
			panic("mark: " + err.Error())
		}
	}
}

// Data: what the snapshot stream carries (64 KiB: 16 blocks, so that a torn data write would show).
func Data() []byte { return bytes.Repeat([]byte("snapdata"), 8192) }

func syncDir(d string) error {
	f, err := os.Open(d)
	if err != nil {
		return err
	}
	defer f.Close()
	return f.Sync()
}

func main() {
	root, sc := os.Args[1], os.Args[2]
	sleep := 1200
	if len(os.Args) > 3 {
		sleep, _ = strconv.Atoi(os.Args[3])
	}
	pause := func() { time.Sleep(time.Duration(sleep) * time.Millisecond) }
	tmp, fn := root+"/tmp1", root+"/0000000000000005.snap.db"
	var want error
	switch sc {
	case "snapsave":
	case "snapsave-exist":
		want = os.ErrExist
	default:
		panic("unknown scenario " + sc)
	}
	var f *os.File
	op("create:tmp1", nil, func() (err error) {
		f, err = os.OpenFile(tmp, os.O_RDWR|os.O_CREATE|os.O_EXCL, 0o600)
		return
	})
	pause()
	op("write:tmp1", nil, func() error { _, err := f.Write(Data()); return err })
	op("fsync:tmp1", nil, func() error { return f.Sync() })
	f.Close()
	pause()
	op("link:tmp1:snapdb", want, func() error { return os.Link(tmp, fn) })
	pause()
	op("unlink:tmp1", nil, func() error { return os.Remove(tmp) })
	pause()
	op("fsyncdir:root", nil, func() error { return syncDir(root) })
}

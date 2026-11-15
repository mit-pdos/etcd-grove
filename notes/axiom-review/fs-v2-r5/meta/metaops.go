// fs-v2-r5, item (b): the metadata calls the walfs, crashlog and bboltfs proofs rely on, run on a
// filesystem of configuration C under dm-log-writes (meta.sh), so that replay.py can rebuild the
// disk at every flush/FUA point and check each crash image against the model's journal order
// (Tree.lean's Follows, Closed). Each call is printed as "OP name begin_ns end_ns" (CLOCK_MONOTONIC)
// so the checker knows which calls returned before which began.
//
// Usage: metaops ROOT SCENARIO [SLEEP_MS]
//
//	segdir    walfs's segdir commit from a leftover: unlink seg.tmp; create seg.tmp; write 8
//	          bytes; fdatasync; rename seg.tmp seg; fsync ROOT
//	dirswap   walfs's dirswap Create: mkdir wal.tmp; create wal.tmp/seg; write 8; fsync;
//	          rename wal.tmp wal; fsync ROOT
//	crashlog  crashlog's commit: create log; write 8 at 0; fdatasync; write 1 at 8; fdatasync
//	replace   rename over a synced file: create tmp; write 8; fsync; rename tmp target (target
//	          holds "old....." synced); fsync ROOT
//	overlap   two threads, each creating N files in its own directory (a/, b/) and renaming each
//	          one in that directory (x -> y), with no sync: calls in different directories
//	          overlapping
//	xrename   two threads renaming files across directories (a/fK -> c/aK, b/fK -> c/bK)
//
// SLEEP_MS between the calls of the sequential scenarios (default 1200, with commit=1: each call's
// transaction commits on its own, so the replay sees every prefix).
package main

import (
	"fmt"
	"os"
	"os/exec"
	"runtime"
	"strconv"
	"sync"
	"syscall"
	"time"
)

var mu sync.Mutex

// now: monotonic nanoseconds since the start (time.Since reads Go's monotonic clock).
func now() int64 { return time.Since(t0).Nanoseconds() }

var t0 = time.Now()

func op(name string, f func() error) {
	b := now()
	err := f()
	e := now()
	mu.Lock()
	fmt.Printf("OP %s %d %d %v\n", name, b, e, err)
	mu.Unlock()
	if err != nil {
		panic(name + ": " + err.Error())
	}
	mark(name)
}

// mark puts a mark in the dm-log-writes log once a call has returned ($LWMARK: the target's name;
// only for the sequential scenarios), so that replay.py knows which crash points come after it.
func mark(name string) {
	if lw := os.Getenv("LWMARK"); lw != "" {
		if err := exec.Command("dmsetup", "message", lw, "0", "mark", name).Run(); err != nil {
			panic("mark: " + err.Error())
		}
	}
}

func data() []byte { return []byte{0xde, 0xad, 0xbe, 0xef, 0x01, 0x23, 0x45, 0x67} }

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
	var f *os.File
	switch sc {
	case "segdir":
		op("unlink:seg.tmp", func() error { return os.Remove(root + "/seg.tmp") })
		pause()
		op("create:seg.tmp", func() (err error) {
			f, err = os.OpenFile(root+"/seg.tmp", os.O_RDWR|os.O_CREATE, 0o666)
			return
		})
		pause()
		op("write:seg.tmp", func() error { _, err := f.WriteAt(data(), 0); return err })
		op("fdatasync:seg.tmp", func() error { return syscall.Fdatasync(int(f.Fd())) })
		f.Close()
		pause()
		op("rename:seg.tmp:seg", func() error { return os.Rename(root+"/seg.tmp", root+"/seg") })
		pause()
		op("fsyncdir:root", func() error { return syncDir(root) })
	case "dirswap":
		op("mkdir:wal.tmp", func() error { return os.Mkdir(root+"/wal.tmp", 0o750) })
		pause()
		op("create:wal.tmp/seg", func() (err error) {
			f, err = os.OpenFile(root+"/wal.tmp/seg", os.O_RDWR|os.O_CREATE, 0o666)
			return
		})
		pause()
		op("write:seg", func() error { _, err := f.WriteAt(data(), 0); return err })
		op("fsync:seg", func() error { return f.Sync() })
		f.Close()
		pause()
		op("rename:wal.tmp:wal", func() error { return os.Rename(root+"/wal.tmp", root+"/wal") })
		pause()
		op("fsyncdir:root", func() error { return syncDir(root) })
	case "crashlog":
		op("create:log", func() (err error) {
			f, err = os.OpenFile(root+"/log", os.O_RDWR|os.O_CREATE, 0o666)
			return
		})
		pause()
		op("write:data", func() error { _, err := f.WriteAt(data(), 0); return err })
		op("fdatasync:1", func() error { return syscall.Fdatasync(int(f.Fd())) })
		pause()
		op("write:flag", func() error { _, err := f.WriteAt([]byte{1}, 8); return err })
		op("fdatasync:2", func() error { return syscall.Fdatasync(int(f.Fd())) })
		f.Close()
	case "replace":
		op("create:tmp", func() (err error) {
			f, err = os.OpenFile(root+"/tmp", os.O_RDWR|os.O_CREATE, 0o666)
			return
		})
		op("write:tmp", func() error { _, err := f.WriteAt([]byte("new....."), 0); return err })
		op("fsync:tmp", func() error { return f.Sync() })
		f.Close()
		pause()
		op("rename:tmp:target", func() error { return os.Rename(root+"/tmp", root+"/target") })
		pause()
		op("fsyncdir:root", func() error { return syncDir(root) })
	case "overlap", "xrename":
		n := 400
		var wg sync.WaitGroup
		for _, d := range []string{"a", "b"} {
			wg.Add(1)
			go func(d string) {
				defer wg.Done()
				runtime.LockOSThread()
				for k := 0; k < n; k++ {
					x := fmt.Sprintf("%s/%s/x%d", root, d, k)
					y := fmt.Sprintf("%s/%s/y%d", root, d, k)
					if sc == "overlap" {
						op("create:"+d+":"+strconv.Itoa(k), func() error {
							g, err := os.OpenFile(x, os.O_RDWR|os.O_CREATE, 0o666)
							if err == nil {
								g.Close()
							}
							return err
						})
						op("rename:"+d+":"+strconv.Itoa(k), func() error { return os.Rename(x, y) })
					} else {
						z := fmt.Sprintf("%s/c/%s%d", root, d, k)
						op("xrename:"+d+":"+strconv.Itoa(k), func() error {
							return os.Rename(fmt.Sprintf("%s/%s/f%d", root, d, k), z)
						})
					}
					time.Sleep(time.Duration(sleep) * time.Microsecond)
				}
			}(d)
		}
		wg.Wait()
	default:
		panic("unknown scenario " + sc)
	}
}

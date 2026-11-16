// Package events writes a driver's process events into a conformance trace directory
// (examples/net/conform/README.md, "Driver files"): when a driver (proctest, the probe) started
// a node's process, when it sent SIGKILL to one, and when one ended, with its exit status. A
// node's crash, for the checker, is the end of one of its processes; the traced processes
// cannot record their own end (a SIGKILL leaves no last word), so the process that waits for
// them does.
//
// The file is _driver.<pid>.<t>.jsonl: a header record ("H", role "driver") and "P" records,
// each one JSON line written with one write(2). Times are CLOCK_MONOTONIC, the clock of the
// nodes' records (runtime.nanotime).
package events

import (
	"encoding/json"
	"fmt"
	"os"
	"path/filepath"
	"runtime"
	"sync"
	"syscall"
	"time"
	"unsafe"
)

// Version is the trace format's version (README.md); the tracer's nettcpVersion.
const Version = 1

// Mono is CLOCK_MONOTONIC in nanoseconds: on Linux, what runtime.nanotime returns, so a driver's
// times and its nodes' are points on one clock.
func Mono() int64 {
	var ts syscall.Timespec
	const clockMonotonic = 1
	if _, _, e := syscall.Syscall(syscall.SYS_CLOCK_GETTIME, clockMonotonic, uintptr(unsafe.Pointer(&ts)), 0); e != 0 {
		panic(fmt.Sprintf("clock_gettime: %v", e))
	}
	return ts.Nano()
}

// Log is a driver's event file.
type Log struct {
	mu   sync.Mutex
	f    *os.File
	pid  int
	node string
	seq  int64
}

// Open creates dir's event file for this process, the driver named node.
func Open(dir, node string) (*Log, error) {
	t := Mono()
	pid := os.Getpid()
	name := filepath.Join(dir, fmt.Sprintf("_driver.%d.%d.jsonl", pid, t))
	f, err := os.OpenFile(name, os.O_CREATE|os.O_WRONLY|os.O_APPEND|os.O_EXCL, 0o644)
	if err != nil {
		return nil, err
	}
	l := &Log{f: f, pid: pid, node: node}
	exe, _ := os.Executable()
	host, _ := os.Hostname()
	tns, _ := os.Readlink("/proc/self/ns/time")
	netns, _ := os.Readlink("/proc/self/ns/net")
	t0 := Mono()
	wall := time.Now().UnixNano()
	t1 := Mono()
	h := map[string]any{
		"k": "H", "v": Version, "role": "driver", "pid": pid, "ppid": os.Getppid(), "node": node,
		"exe": exe, "args": os.Args, "go": runtime.Version(), "host": host, "timens": tns,
		"netns": netns, "file": name, "t0": t0, "wall": wall, "t1": t1,
	}
	if err := l.write(h); err != nil {
		f.Close()
		return nil, err
	}
	return l, nil
}

func (l *Log) write(rec map[string]any) error {
	b, err := json.Marshal(rec)
	if err != nil {
		return err
	}
	_, err = l.f.Write(append(b, '\n'))
	return err
}

func (l *Log) event(ev string, cnode string, cpid int, t int64, extra map[string]any) {
	if l == nil {
		return
	}
	l.mu.Lock()
	defer l.mu.Unlock()
	l.seq++
	rec := map[string]any{"k": "P", "pid": l.pid, "node": l.node, "s": l.seq, "ev": ev, "t": t,
		"cnode": cnode, "cpid": cpid}
	for k, v := range extra {
		rec[k] = v
	}
	if err := l.write(rec); err != nil {
		fmt.Fprintf(os.Stderr, "events: %v\n", err)
	}
}

// Start records that the process p, node cnode, running bin, was started (after its Start
// returned: the process exists; its own records come later).
func (l *Log) Start(cnode string, p *os.Process, bin string) {
	l.event("start", cnode, p.Pid, Mono(), map[string]any{"bin": bin})
}

// Kill records that SIGKILL is about to be sent to process cpid (the time is taken before the
// signal: the process ends between this event and its exit event).
func (l *Log) Kill(cnode string, cpid int) {
	l.event("kill", cnode, cpid, Mono(), nil)
}

// Exit records that process cpid has ended (after its Wait returned) with state st.
func (l *Log) Exit(cnode string, cpid int, st *os.ProcessState) {
	t := Mono()
	extra := map[string]any{"code": -1}
	if st != nil {
		extra["code"] = st.ExitCode()
		if ws, ok := st.Sys().(syscall.WaitStatus); ok && ws.Signaled() {
			extra["signal"] = ws.Signal().String()
			extra["signo"] = int(ws.Signal())
		}
	}
	l.event("exit", cnode, cpid, t, extra)
}

// Close closes the file.
func (l *Log) Close() error {
	if l == nil {
		return nil
	}
	return l.f.Close()
}

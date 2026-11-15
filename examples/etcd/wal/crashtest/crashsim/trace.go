// Package crashsim records the file-system system calls a process makes under a directory (a
// ptrace tracer, no new dependency) and replays them into crash images under three models: kill -9
// (the page cache survives), power loss under the bare fsync(2) contract, and power loss under
// journal ordering.
package crashsim

import (
	"bufio"
	"bytes"
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
	"runtime"
	"strconv"
	"strings"
	"syscall"
)

// Kind is the kind of a recorded event.
type Kind int

const (
	KWrite  Kind = iota // data write at Off
	KTrunc              // size set to Size (ftruncate, open O_TRUNC)
	KFalloc             // fallocate(Mode, Off, Size-Off)
	KSync               // fsync (DataOnly false) or fdatasync (DataOnly true)
	KCreate             // a new file Ino named Name in Parent
	KMkdir              // a new directory Ino named Name in Parent
	KUnlink             // Name (inode Ino) removed from Parent
	KRename             // Parent/Name -> Parent2/Name2 (Ino; Replaced overwritten, or 0)
	KMarker             // a marker the traced program wrote (Marker)
)

func (k Kind) String() string {
	return [...]string{"write", "trunc", "falloc", "sync", "create", "mkdir", "unlink", "rename", "marker"}[k]
}

// Event is one recorded system call, at its exit (its effect done).
type Event struct {
	Kind     Kind
	Ino      uint64
	Dir      bool
	DataOnly bool
	Off      int64
	Data     []byte
	Size     int64
	Mode     int
	Parent   uint64
	Name     string
	Parent2  uint64
	Name2    string
	Replaced uint64
	Marker   string
	Path     string
}

func (e Event) String() string {
	switch e.Kind {
	case KWrite:
		return fmt.Sprintf("write ino=%d off=%d len=%d %s", e.Ino, e.Off, len(e.Data), e.Path)
	case KTrunc:
		return fmt.Sprintf("trunc ino=%d size=%d %s", e.Ino, e.Size, e.Path)
	case KFalloc:
		return fmt.Sprintf("falloc ino=%d mode=%d off=%d end=%d %s", e.Ino, e.Mode, e.Off, e.Size, e.Path)
	case KSync:
		return fmt.Sprintf("sync ino=%d dir=%v dataonly=%v %s", e.Ino, e.Dir, e.DataOnly, e.Path)
	case KCreate, KMkdir, KUnlink:
		return fmt.Sprintf("%s %d/%s ino=%d %s", e.Kind, e.Parent, e.Name, e.Ino, e.Path)
	case KRename:
		return fmt.Sprintf("rename %d/%s -> %d/%s ino=%d replaced=%d %s", e.Parent, e.Name, e.Parent2, e.Name2, e.Ino, e.Replaced, e.Path)
	case KMarker:
		return "marker " + e.Marker
	}
	return "?"
}

// amd64 system call numbers.
const (
	sysWrite         = 1
	sysOpen          = 2
	sysPwrite64      = 18
	sysWritev        = 20
	sysSendfile      = 40
	sysFsync         = 74
	sysFdatasync     = 75
	sysTruncate      = 76
	sysFtruncate     = 77
	sysRename        = 82
	sysMkdir         = 83
	sysRmdir         = 84
	sysCreat         = 85
	sysLink          = 86
	sysUnlink        = 87
	sysOpenat        = 257
	sysMkdirat       = 258
	sysUnlinkat      = 263
	sysRenameat      = 264
	sysLinkat        = 265
	sysSplice        = 275
	sysSyncFileRange = 277
	sysFallocate     = 285
	sysPwritev       = 296
	sysRenameat2     = 316
	sysCopyFileRange = 326
	sysPwritev2      = 328
	atFdcwd          = -100
	ptraceOExitkill  = 0x100000
)

type pending struct {
	nr     uint64
	skip   bool
	ev     Event
	buf    uint64
	path   string // resolved path (open, mkdir)
	exists bool
	flags  int
	marker bool
}

type tracer struct {
	root    string
	marker  string
	tgid    int
	mem     *os.File
	inSys   map[int]bool
	pend    map[int]*pending
	events  []Event
	errs    []string
	verbose bool
}

func (t *tracer) under(p string) bool {
	p = strings.TrimSuffix(p, " (deleted)")
	return p == t.root || strings.HasPrefix(p, t.root+"/")
}

func (t *tracer) readMem(addr uint64, n int) []byte {
	b := make([]byte, n)
	got := 0
	for got < n {
		k, err := t.mem.ReadAt(b[got:], int64(addr)+int64(got))
		if k <= 0 || err != nil && k == 0 {
			t.errs = append(t.errs, fmt.Sprintf("readMem %x+%d: %v", addr, got, err))
			break
		}
		got += k
	}
	return b[:got]
}

func (t *tracer) readStr(addr uint64) string {
	var out []byte
	for len(out) < 8192 {
		chunk := make([]byte, 128)
		k, _ := t.mem.ReadAt(chunk, int64(addr)+int64(len(out)))
		if k <= 0 {
			break
		}
		if i := bytes.IndexByte(chunk[:k], 0); i >= 0 {
			return string(append(out, chunk[:i]...))
		}
		out = append(out, chunk[:k]...)
	}
	return string(out)
}

func (t *tracer) resolve(tid int, dirfd int32, p string) string {
	if filepath.IsAbs(p) {
		return filepath.Clean(p)
	}
	var base string
	if dirfd == atFdcwd {
		base, _ = os.Readlink(fmt.Sprintf("/proc/%d/cwd", tid))
	} else {
		base, _ = os.Readlink(fmt.Sprintf("/proc/%d/fd/%d", tid, dirfd))
	}
	return filepath.Clean(filepath.Join(base, p))
}

func lstatIno(p string) (uint64, bool, bool) {
	var st syscall.Stat_t
	if err := syscall.Lstat(p, &st); err != nil {
		return 0, false, false
	}
	return st.Ino, st.Mode&syscall.S_IFMT == syscall.S_IFDIR, true
}

func fdPath(tid int, fd int) string {
	p, _ := os.Readlink(fmt.Sprintf("/proc/%d/fd/%d", tid, fd))
	return p
}

func fdIno(tid int, fd int) (uint64, bool) {
	var st syscall.Stat_t
	if err := syscall.Stat(fmt.Sprintf("/proc/%d/fd/%d", tid, fd), &st); err != nil {
		return 0, false
	}
	return st.Ino, st.Mode&syscall.S_IFMT == syscall.S_IFDIR
}

func fdPos(tid int, fd int) int64 {
	f, err := os.Open(fmt.Sprintf("/proc/%d/fdinfo/%d", tid, fd))
	if err != nil {
		return -1
	}
	defer f.Close()
	sc := bufio.NewScanner(f)
	for sc.Scan() {
		if v, ok := strings.CutPrefix(sc.Text(), "pos:"); ok {
			n, _ := strconv.ParseInt(strings.TrimSpace(v), 10, 64)
			return n
		}
	}
	return -1
}

func parentIno(p string) uint64 {
	ino, _, _ := lstatIno(filepath.Dir(p))
	return ino
}

func (t *tracer) entry(tid int, r *syscall.PtraceRegs) {
	nr := r.Orig_rax
	a := [6]uint64{r.Rdi, r.Rsi, r.Rdx, r.R10, r.R8, r.R9}
	p := &pending{nr: nr, skip: true}
	t.pend[tid] = p
	fdOp := func(fd int) (string, bool) {
		path := fdPath(tid, fd)
		return path, t.under(path)
	}
	switch nr {
	case sysWrite, sysPwrite64:
		fd := int(int32(a[0]))
		path := fdPath(tid, fd)
		if path == t.marker {
			p.skip, p.marker, p.buf = false, true, a[1]
			p.ev = Event{Kind: KMarker}
			return
		}
		if !t.under(path) {
			return
		}
		ino, _ := fdIno(tid, fd)
		off := int64(a[3])
		if nr == sysWrite {
			off = fdPos(tid, fd)
		}
		p.skip, p.buf = false, a[1]
		p.ev = Event{Kind: KWrite, Ino: ino, Off: off, Path: path}
	case sysFtruncate:
		fd := int(int32(a[0]))
		if path, ok := fdOp(fd); ok {
			ino, _ := fdIno(tid, fd)
			p.skip = false
			p.ev = Event{Kind: KTrunc, Ino: ino, Size: int64(a[1]), Path: path}
		}
	case sysTruncate:
		path := t.resolve(tid, atFdcwd, t.readStr(a[0]))
		if t.under(path) {
			ino, _, _ := lstatIno(path)
			p.skip = false
			p.ev = Event{Kind: KTrunc, Ino: ino, Size: int64(a[1]), Path: path}
		}
	case sysFallocate:
		fd := int(int32(a[0]))
		if path, ok := fdOp(fd); ok {
			ino, _ := fdIno(tid, fd)
			p.skip = false
			p.ev = Event{Kind: KFalloc, Ino: ino, Mode: int(a[1]), Off: int64(a[2]), Size: int64(a[2] + a[3]), Path: path}
		}
	case sysFsync, sysFdatasync:
		fd := int(int32(a[0]))
		if path, ok := fdOp(fd); ok {
			ino, dir := fdIno(tid, fd)
			p.skip = false
			p.ev = Event{Kind: KSync, Ino: ino, Dir: dir, DataOnly: nr == sysFdatasync, Path: path}
		}
	case sysOpenat, sysOpen, sysCreat:
		var path string
		var flags int
		switch nr {
		case sysOpenat:
			path = t.resolve(tid, int32(a[0]), t.readStr(a[1]))
			flags = int(a[2])
		case sysOpen:
			path = t.resolve(tid, atFdcwd, t.readStr(a[0]))
			flags = int(a[1])
		case sysCreat:
			path = t.resolve(tid, atFdcwd, t.readStr(a[0]))
			flags = syscall.O_CREAT | syscall.O_WRONLY | syscall.O_TRUNC
		}
		if !t.under(path) || path == t.root {
			return
		}
		_, _, exists := lstatIno(path)
		p.skip, p.path, p.flags, p.exists = false, path, flags, exists
	case sysMkdirat, sysMkdir:
		var path string
		if nr == sysMkdirat {
			path = t.resolve(tid, int32(a[0]), t.readStr(a[1]))
		} else {
			path = t.resolve(tid, atFdcwd, t.readStr(a[0]))
		}
		if t.under(path) && path != t.root {
			p.skip, p.path = false, path
		}
	case sysUnlinkat, sysUnlink, sysRmdir:
		var path string
		if nr == sysUnlinkat {
			path = t.resolve(tid, int32(a[0]), t.readStr(a[1]))
		} else {
			path = t.resolve(tid, atFdcwd, t.readStr(a[0]))
		}
		if t.under(path) && path != t.root {
			ino, dir, ok := lstatIno(path)
			if ok {
				p.skip = false
				p.ev = Event{Kind: KUnlink, Ino: ino, Dir: dir, Parent: parentIno(path), Name: filepath.Base(path), Path: path}
			}
		}
	case sysRenameat, sysRenameat2, sysRename:
		var src, dst string
		if nr == sysRename {
			src = t.resolve(tid, atFdcwd, t.readStr(a[0]))
			dst = t.resolve(tid, atFdcwd, t.readStr(a[1]))
		} else {
			src = t.resolve(tid, int32(a[0]), t.readStr(a[1]))
			dst = t.resolve(tid, int32(a[2]), t.readStr(a[3]))
		}
		if t.under(src) || t.under(dst) {
			if !t.under(src) || !t.under(dst) {
				t.errs = append(t.errs, fmt.Sprintf("rename across the root: %s -> %s", src, dst))
				return
			}
			ino, dir, _ := lstatIno(src)
			repl, _, _ := lstatIno(dst)
			p.skip = false
			p.ev = Event{Kind: KRename, Ino: ino, Dir: dir, Parent: parentIno(src), Name: filepath.Base(src),
				Parent2: parentIno(dst), Name2: filepath.Base(dst), Replaced: repl, Path: src + " -> " + dst}
		}
	case sysWritev, sysPwritev, sysPwritev2, sysSendfile, sysCopyFileRange, sysSplice, sysSyncFileRange:
		fd := int(int32(a[0]))
		if nr == sysSendfile || nr == sysSplice || nr == sysCopyFileRange {
			fd = int(int32(a[1]))
			if nr == sysSplice || nr == sysCopyFileRange {
				fd = int(int32(a[2]))
			}
		}
		// wal.Repair's backup copy (*.wal.broken, io.Copy: copy_file_range) is never read by the
		// WAL: its content is not recorded (the file exists in the image, empty)
		if path, ok := fdOp(fd); ok && !strings.HasSuffix(path, ".broken") {
			t.errs = append(t.errs, fmt.Sprintf("unsupported system call %d on %s", nr, path))
		}
	case sysLink, sysLinkat:
		t.errs = append(t.errs, fmt.Sprintf("unsupported system call %d (link)", nr))
	}
}

func (t *tracer) exit(tid int, r *syscall.PtraceRegs) {
	p := t.pend[tid]
	delete(t.pend, tid)
	if p == nil || p.skip {
		return
	}
	ret := int64(r.Rax)
	if ret < 0 {
		return
	}
	switch p.nr {
	case sysWrite, sysPwrite64:
		if ret == 0 {
			return
		}
		data := t.readMem(p.buf, int(ret))
		if p.marker {
			p.ev.Marker = string(data)
		} else {
			p.ev.Data = data
		}
	case sysOpenat, sysOpen, sysCreat:
		fd := int(ret)
		ino, dir := fdIno(tid, fd)
		if p.flags&syscall.O_CREAT != 0 && !p.exists {
			p.ev = Event{Kind: KCreate, Ino: ino, Parent: parentIno(p.path), Name: filepath.Base(p.path), Path: p.path}
		} else if p.flags&syscall.O_TRUNC != 0 && p.exists && !dir && p.flags&syscall.O_ACCMODE != syscall.O_RDONLY {
			p.ev = Event{Kind: KTrunc, Ino: ino, Size: 0, Path: p.path}
		} else {
			return
		}
	case sysMkdirat, sysMkdir:
		ino, _, _ := lstatIno(p.path)
		p.ev = Event{Kind: KMkdir, Ino: ino, Dir: true, Parent: parentIno(p.path), Name: filepath.Base(p.path), Path: p.path}
	}
	if t.verbose {
		fmt.Fprintln(os.Stderr, "TRACE", tid, p.ev)
	}
	t.events = append(t.events, p.ev)
}

// Record runs cmd under ptrace and returns the file-system events under root (and the markers
// written to the file markerPath), in the order of their system calls' exits. root and markerPath
// must be canonical absolute paths.
func Record(root, markerPath string, cmd *exec.Cmd) ([]Event, error) {
	runtime.LockOSThread()
	defer runtime.UnlockOSThread()
	if cmd.SysProcAttr == nil {
		cmd.SysProcAttr = &syscall.SysProcAttr{}
	}
	cmd.SysProcAttr.Ptrace = true
	if err := cmd.Start(); err != nil {
		return nil, err
	}
	pid := cmd.Process.Pid
	var ws syscall.WaitStatus
	if _, err := syscall.Wait4(pid, &ws, syscall.WALL, nil); err != nil {
		return nil, err
	}
	if err := syscall.PtraceSetOptions(pid, syscall.PTRACE_O_TRACESYSGOOD|syscall.PTRACE_O_TRACECLONE|ptraceOExitkill); err != nil {
		return nil, fmt.Errorf("PtraceSetOptions: %w", err)
	}
	mem, err := os.Open(fmt.Sprintf("/proc/%d/mem", pid))
	if err != nil {
		return nil, err
	}
	defer mem.Close()
	t := &tracer{root: root, marker: markerPath, tgid: pid, mem: mem, inSys: map[int]bool{}, pend: map[int]*pending{},
		verbose: os.Getenv("CRASHSIM_VERBOSE") != ""}
	if err := syscall.PtraceSyscall(pid, 0); err != nil {
		return nil, err
	}
	exitCode := -1
	for {
		tid, err := syscall.Wait4(-1, &ws, syscall.WALL, nil)
		if err == syscall.ECHILD {
			break
		}
		if err == syscall.EINTR {
			continue
		}
		if err != nil {
			return nil, err
		}
		switch {
		case ws.Exited() || ws.Signaled():
			if tid == pid {
				if ws.Exited() {
					exitCode = ws.ExitStatus()
				} else {
					exitCode = 128 + int(ws.Signal())
				}
			}
			delete(t.inSys, tid)
			continue
		case ws.Stopped():
			sig := ws.StopSignal()
			deliver := 0
			switch {
			case sig == syscall.SIGTRAP|0x80:
				var regs syscall.PtraceRegs
				if err := syscall.PtraceGetRegs(tid, &regs); err == nil {
					if !t.inSys[tid] {
						t.inSys[tid] = true
						t.entry(tid, &regs)
					} else {
						t.inSys[tid] = false
						t.exit(tid, &regs)
					}
				}
			case sig == syscall.SIGTRAP:
				// event stop (clone) or exec trap
			case sig == syscall.SIGSTOP:
				// a new thread's initial stop (Go never stops itself)
			default:
				deliver = int(sig)
			}
			syscall.PtraceSyscall(tid, deliver)
		}
	}
	if len(t.errs) > 0 {
		return t.events, fmt.Errorf("tracer: %s", strings.Join(t.errs, "; "))
	}
	if exitCode != 0 {
		return t.events, fmt.Errorf("traced process exited with %d", exitCode)
	}
	return t.events, nil
}

// pw: what a buffered pwrite(2) returns on configuration C when it cannot write everything, and
// what the page cache holds afterwards. Each case writes a pattern (never zero) at OFF, records
// the result -- of one unix.Pwrite system call ("sys") or of os.File.WriteAt's loop ("go") --
// then preads the range back (the page cache) and reports the landed prefix.
//
//	pw enospc DIR      ENOSPC mid-write on a nearly full filesystem (DIR on it)
//	pw efbig DIR       writes ending past s_maxbytes, and one at it (EFBIG)
//	pw rlimit DIR      contrast (not C): RLIMIT_FSIZE = 10000
//	pw signals DIR     a 256 MiB write while signals arrive; a source of untouched mmap pages
//	pw efault DIR      contrast (not Go memory): a source page PROT_NONE
//	pw shutdown DIR    contrast (not C): FS_IOC_SHUTDOWN during a 512 MiB write
package main

import (
	"errors"
	"fmt"
	"os"
	"os/exec"
	"os/signal"
	"path/filepath"
	"syscall"
	"time"

	"golang.org/x/sys/unix"
)

const page = 4096

// pat is the byte the pattern puts at file offset x: never zero.
func pat(x uint64) byte { return byte((x*7+13)%251) + 1 }

func buf(off uint64, n int) []byte {
	b := make([]byte, n)
	for i := range b {
		b[i] = pat(off + uint64(i))
	}
	return b
}

func must(err error) {
	if err != nil {
		panic(err)
	}
}

// write writes data at off by mode "sys" (one pwrite) or "go" (os.File.WriteAt): (n, errno text).
func write(f *os.File, mode string, data []byte, off int64) (int, string) {
	if mode == "sys" {
		n, err := unix.Pwrite(int(f.Fd()), data, off)
		if err != nil {
			return n, err.(unix.Errno).Error() + fmt.Sprintf(" (errno %d)", int(err.(unix.Errno)))
		}
		return n, "nil"
	}
	n, err := f.WriteAt(data, off)
	if err != nil {
		var pe *os.PathError
		if errors.As(err, &pe) {
			return n, pe.Err.Error()
		}
		return n, err.Error()
	}
	return n, "nil"
}

// landed reads [off, off+span) back and returns the length of the pattern's prefix at off and
// the count of pattern bytes after it (bytes of the write beyond the landed prefix).
func landed(f *os.File, off int64, span int) (int, int) {
	r := make([]byte, span)
	m, _ := unix.Pread(int(f.Fd()), r, off)
	if m < 0 {
		m = 0
	}
	p := 0
	for p < m && r[p] == pat(uint64(off)+uint64(p)) {
		p++
	}
	beyond := 0
	for i := p; i < m; i++ {
		if r[i] != 0 && r[i] == pat(uint64(off)+uint64(i)) {
			beyond++
		}
	}
	return p, beyond
}

func size(f *os.File) int64 {
	st, err := f.Stat()
	must(err)
	return st.Size()
}

func report(name, mode string, off int64, l int, size0 int64, n int, e string, f *os.File) {
	p, beyond := landed(f, off, l+2*page)
	end := "-"
	if n > 0 {
		end = fmt.Sprint((off + int64(n)) % page)
	}
	fmt.Printf("%-28s %-3s off=%-14d len=%-8d -> n=%-8d err=%-28s | (off+n)%%4096=%-4s landed=%-8d (off+landed)%%4096=%-4d beyond=%d size %d->%d\n",
		name, mode, off, l, n, e, end, p, (off+int64(p))%page, beyond, size0, size(f))
}

func avail(dir string) uint64 {
	var s unix.Statfs_t
	must(unix.Statfs(dir, &s))
	return s.Bavail
}

func syncfs(dir string) {
	f, err := os.Open(dir)
	must(err)
	must(unix.Syncfs(int(f.Fd())))
	f.Close()
}

// fill leaves about `left` blocks available to this (non-root) user.
func fill(dir string, left uint64) {
	for {
		syncfs(dir)
		a := avail(dir)
		if a <= left {
			return
		}
		f, err := os.OpenFile(filepath.Join(dir, fmt.Sprintf("filler-%d", time.Now().UnixNano())), os.O_RDWR|os.O_CREATE, 0o644)
		must(err)
		k := a - left
		for k > 0 && unix.Fallocate(int(f.Fd()), 0, 0, int64(k)*page) != nil {
			k /= 2
		}
		f.Close()
		if k == 0 {
			return
		}
	}
}

func enospc(dir string) {
	type cs struct {
		name string
		pre  int64 // existing file size (a synced prefix), for the gap case
		off  int64
		l    int
		left uint64
	}
	cases := []cs{
		{"aligned 16 pages", 0, 0, 16 * page, 0},
		{"unaligned 100, 16p+300", 0, 100, 16*page + 300, 0},
		{"unaligned 4000, 16p+300", 0, 4000, 16*page + 300, 0},
		{"unaligned 100, 8 MiB", 0, 100, 8 << 20, 0},
		{"gap: size 8192, off 5p+100", 8192, 5*page + 100, 16 * page, 0},
		{"one aligned page", 0, 0, page, 0},
		{"unaligned 3000, 1 page", 0, 3000, page, 0},
	}
	// a sweep of the blocks left available (statfs f_bavail, this non-root user's view)
	lefts := []uint64{0, 4, 8, 12, 16, 20, 24, 32, 48, 64, 256, 1024, 2048, 3072}
	for _, mode := range []string{"sys", "go"} {
		for i, c := range cases {
			for _, left := range lefts {
				if c.l < 1<<20 && left > 64 {
					continue
				}
				clean(dir)
				p := filepath.Join(dir, fmt.Sprintf("f-%s-%d", mode, i))
				f, err := os.OpenFile(p, os.O_RDWR|os.O_CREATE|os.O_TRUNC, 0o644)
				must(err)
				if c.pre > 0 {
					_, err = f.WriteAt(make([]byte, c.pre), 0)
					must(err)
					must(f.Sync())
				}
				fill(dir, left)
				a0 := avail(dir)
				s0 := size(f)
				n, e := write(f, mode, buf(uint64(c.off), c.l), c.off)
				report(c.name+fmt.Sprintf(" [avail %d]", a0), mode, c.off, c.l, s0, n, e, f)
				f.Close()
			}
		}
	}
	clean(dir)
}

func clean(dir string) {
	ms, _ := filepath.Glob(filepath.Join(dir, "*"))
	for _, m := range ms {
		os.Remove(m)
	}
	syncfs(dir)
}

const maxBytes = int64(0xffffffff) << 12 // ext4_max_size: (2^32-1) << 12 = 2^44 - 4096

func efbig(dir string) {
	type cs struct {
		name string
		off  int64
		l    int
	}
	cases := []cs{
		{"end at max, 100 before", maxBytes - 100, 8192},
		{"end at max, 5000 before", maxBytes - 5000, 3 * page},
		{"at s_maxbytes", maxBytes, 100},
		{"at s_maxbytes+1", maxBytes + 1, 100},
	}
	for _, mode := range []string{"sys", "go"} {
		for i, c := range cases {
			f, err := os.OpenFile(filepath.Join(dir, fmt.Sprintf("big-%s-%d", mode, i)), os.O_RDWR|os.O_CREATE|os.O_TRUNC, 0o644)
			must(err)
			s0 := size(f)
			n, e := write(f, mode, buf(uint64(c.off), c.l), c.off)
			report(c.name, mode, c.off, c.l, s0, n, e, f)
			f.Close()
		}
	}
}

func rlimit(dir string) {
	signal.Ignore(syscall.SIGXFSZ)
	must(unix.Setrlimit(unix.RLIMIT_FSIZE, &unix.Rlimit{Cur: 10000, Max: 10000}))
	for _, mode := range []string{"sys", "go"} {
		f, err := os.OpenFile(filepath.Join(dir, "rl-"+mode), os.O_RDWR|os.O_CREATE|os.O_TRUNC, 0o644)
		must(err)
		n, e := write(f, mode, buf(8000, 8192), 8000)
		report("RLIMIT_FSIZE 10000", mode, 8000, 8192, 0, n, e, f)
		n, e = write(f, mode, buf(10000, 100), 10000)
		report("RLIMIT_FSIZE 10000, at it", mode, 10000, 100, 10000, n, e, f)
		f.Close()
	}
}

func signals(dir string) {
	ch := make(chan os.Signal, 1)
	signal.Notify(ch, syscall.SIGUSR1)
	go func() {
		for range ch {
		}
	}()
	stop := make(chan struct{})
	sent := 0
	go func() {
		for {
			select {
			case <-stop:
				return
			default:
				syscall.Kill(os.Getpid(), syscall.SIGUSR1)
				sent++
				time.Sleep(20 * time.Microsecond)
			}
		}
	}()
	const L = 256 << 20
	for _, mode := range []string{"sys", "go"} {
		f, err := os.OpenFile(filepath.Join(dir, "sig-"+mode), os.O_RDWR|os.O_CREATE|os.O_TRUNC, 0o644)
		must(err)
		for rep := 0; rep < 3; rep++ {
			t := time.Now()
			n, e := write(f, mode, buf(100, L), 100)
			fmt.Printf("signals %s rep %d: n=%d (len %d) err=%s in %v\n", mode, rep, n, L, e, time.Since(t))
		}
		f.Close()
		os.Remove(filepath.Join(dir, "sig-"+mode))
	}
	close(stop)
	fmt.Printf("signals sent: %d\n", sent)
	// a source of untouched (not present) anonymous pages, at an unaligned file offset
	for _, mode := range []string{"sys", "go"} {
		src, err := unix.Mmap(-1, 0, 64*page, unix.PROT_READ|unix.PROT_WRITE, unix.MAP_PRIVATE|unix.MAP_ANONYMOUS)
		must(err)
		f, err := os.OpenFile(filepath.Join(dir, "np-"+mode), os.O_RDWR|os.O_CREATE|os.O_TRUNC, 0o644)
		must(err)
		n, e := write(f, mode, src, 100)
		fmt.Printf("untouched mmap source %s: off 100 len %d -> n=%d err=%s\n", mode, len(src), n, e)
		f.Close()
		unix.Munmap(src)
	}
}

func efault(dir string) {
	for _, mode := range []string{"sys", "go"} {
		src, err := unix.Mmap(-1, 0, 3*page, unix.PROT_READ|unix.PROT_WRITE, unix.MAP_PRIVATE|unix.MAP_ANONYMOUS)
		must(err)
		copy(src, buf(100, 3*page))
		must(unix.Mprotect(src[2*page:], unix.PROT_NONE))
		f, err := os.OpenFile(filepath.Join(dir, "ef-"+mode), os.O_RDWR|os.O_CREATE|os.O_TRUNC, 0o644)
		must(err)
		n, e := write(f, mode, src, 100)
		report("source page 2 PROT_NONE", mode, 100, 3*page, 0, n, e, f)
		f.Close()
	}
}

func shutdown(dir string) {
	const L = 512 << 20
	f, err := os.OpenFile(filepath.Join(dir, "sd"), os.O_RDWR|os.O_CREATE|os.O_TRUNC, 0o644)
	must(err)
	// pre-size and map the file, so the page cache can be read after the shutdown (pread fails)
	must(f.Truncate(int64(L + 2*page)))
	m, err := unix.Mmap(int(f.Fd()), 0, L+2*page, unix.PROT_READ, unix.MAP_SHARED)
	must(err)
	data := buf(100, L)
	go func() {
		time.Sleep(100 * time.Millisecond)
		// FS_IOC_SHUTDOWN needs CAP_SYS_ADMIN: xfs_io's shutdown (no -f: NOLOGFLUSH), as root
		out, err := exec.Command("sudo", "xfs_io", "-x", "-c", "shutdown", dir).CombinedOutput()
		fmt.Printf("shutdown: %v %s\n", err, out)
	}()
	n, e := write(f, "sys", data, 100)
	p := 0
	for p < L && m[100+p] == pat(100+uint64(p)) {
		p++
	}
	fmt.Printf("shutdown during write: off 100 len %d -> n=%d err=%s end%%4096=%d; mapped page cache: landed prefix %d\n",
		L, n, e, (100+n)%page, p)
}

func main() {
	dir := os.Args[2]
	switch os.Args[1] {
	case "enospc":
		enospc(dir)
	case "efbig":
		efbig(dir)
	case "rlimit":
		rlimit(dir)
	case "signals":
		signals(dir)
	case "efault":
		efault(dir)
	case "shutdown":
		shutdown(dir)
	}
}

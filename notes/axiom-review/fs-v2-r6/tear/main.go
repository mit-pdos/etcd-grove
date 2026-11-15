// fs-v2-r6 (a): does a pwrite from resident, program-written Go memory ever land a prefix that ends
// inside a file page on configuration C (NoTear.lean's "machine assumption" when the buffer is
// aligned)? tear.bt counts ext4_da_write_end calls with copied < len by where the cut lands in the
// file page.
//
// Usage: tear FILE SKEW WSIZE SECONDS [POOLMIB]
//
//	A POOLMIB-MiB []byte (default 256), every byte written by the program; then for SECONDS,
//	pwrite WSIZE bytes starting SKEW bytes into page k of the pool (k cycling) at a file offset
//	that is a WSIZE multiple (a 64 MiB file, written and synced first, so its pages are cached
//	and uptodate). SKEW 0: buffer address ≡ file offset (mod 4096); SKEW 3144 (0xc48):
//	minibolt's commit buffers as measured (addr % 4096 = 0xc48).
package main

import (
	"fmt"
	"os"
	"strconv"
	"time"
	"unsafe"
)

func main() {
	path := os.Args[1]
	skew, _ := strconv.Atoi(os.Args[2])
	ws, _ := strconv.Atoi(os.Args[3])
	secs, _ := strconv.Atoi(os.Args[4])
	poolMiB := 256
	if len(os.Args) > 5 {
		poolMiB, _ = strconv.Atoi(os.Args[5])
	}
	const fileSize = 64 << 20
	f, err := os.OpenFile(path, os.O_RDWR|os.O_CREATE|os.O_TRUNC, 0o644)
	if err != nil {
		panic(err)
	}
	a := make([]byte, 1<<20)
	for i := range a {
		a[i] = 'A'
	}
	for off := 0; off < fileSize; off += len(a) {
		if _, err := f.WriteAt(a, int64(off)); err != nil {
			panic(err)
		}
	}
	if err := f.Sync(); err != nil {
		panic(err)
	}
	// a pool started on a page boundary
	pool := make([]byte, poolMiB<<20+8192)
	base := int((4096 - uintptr(unsafe.Pointer(&pool[0]))%4096) % 4096)
	pool = pool[base:]
	for i := range pool {
		pool[i] = byte('B' + i%7)
	}
	pages := (len(pool) - ws - 8192) / 4096
	end := time.Now().Add(time.Duration(secs) * time.Second)
	n, bytes := 0, 0
	for k := 0; ; k = (k + ws/4096 + 1) % pages {
		if n%1024 == 0 && time.Now().After(end) {
			break
		}
		src := pool[k*4096+skew : k*4096+skew+ws]
		off := (k * 4096) % (fileSize - ws)
		off -= off % ws
		if w, err := f.WriteAt(src, int64(off)); err != nil || w != ws {
			panic(fmt.Sprint(w, err))
		}
		n++
		bytes += ws
	}
	fmt.Printf("skew %d, wsize %d: %d writes, %d source pages copied (addr %% 4096 = %#x)\n",
		skew, ws, n, bytes/4096, (uintptr(unsafe.Pointer(&pool[0]))+uintptr(skew))%4096)
}

// fs-v2-r5, item (a): is a pwrite's source buffer "present while the call runs" on C, as
// NoTear.lean's header assumes? A short atomic copy in generic_perform_write (the source page not
// present) commits the copied prefix of an uptodate folio and unlocks it: a cut where the source
// page ends. notear.bt counts them (copy_folio_from_iter_atomic returning short) for this
// process, with the file offset where the cut lands in its page.
//
// Usage: notear FILE MODE ITERS
//
//	MODE fresh: each iteration a new 1 MiB []byte (fresh Go heap memory, kept live so it is not
//	            reused), of which the program writes only its first 4096 bytes; WriteAt of the
//	            4096 bytes from offset 2148 of it, at file offset 0 (it crosses into the
//	            untouched second page)
//	MODE all:   one 64 MiB []byte, every byte written by the program before the loop; WriteAt of
//	            4096 bytes from offset 2148 of page k (k cycling), at file offset 0 (run with a
//	            compaction loop beside it: migration is what could make a written page absent)
//	MODE aligned: as all, but the source starts on a page (offset 0 of page k), as minibolt's
//	            make([]byte, 4096) and make([]byte, 4*4096) do (size classes 44 and 59 of Go 1.27:
//	            4096-byte alignment)
package main

import (
	"fmt"
	"os"
	"strconv"
)

func main() {
	path, mode := os.Args[1], os.Args[2]
	iters, _ := strconv.Atoi(os.Args[3])
	f, err := os.OpenFile(path, os.O_RDWR|os.O_CREATE|os.O_TRUNC, 0o644)
	if err != nil {
		panic(err)
	}
	a := make([]byte, 8192)
	for i := range a {
		a[i] = 'A'
	}
	if _, err := f.WriteAt(a, 0); err != nil {
		panic(err)
	}
	if err := f.Sync(); err != nil {
		panic(err)
	}
	var keep [][]byte
	var pool []byte
	skew := 2148
	if mode == "aligned" {
		skew = 0
	}
	if mode != "fresh" {
		pool = make([]byte, 64<<20)
		for i := range pool {
			pool[i] = byte('B' + i%7)
		}
	}
	for it := 0; it < iters; it++ {
		var src []byte
		if mode == "fresh" {
			b := make([]byte, 1<<20)
			for i := 0; i < 4096; i++ {
				b[i] = 'B'
			}
			keep = append(keep, b)
			src = b[2148 : 2148+4096]
		} else {
			k := it % (len(pool)/4096 - 2)
			src = pool[k*4096+skew : k*4096+skew+4096]
		}
		if n, err := f.WriteAt(src, 0); err != nil || n != 4096 {
			panic(fmt.Sprint(n, err))
		}
	}
	fmt.Printf("%s: %d writes done (%d buffers kept)\n", mode, iters, len(keep))
}

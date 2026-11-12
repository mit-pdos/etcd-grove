// fs-v2-r6 e2e: the writer and the syncer.
//
//	tearw init DIR N              create DIR/f0..f{N-1}, each one page of 0x00, fsynced
//	tearw write FILE SKEW SECS [POOLMIB [once|each]]
//	                              for SECS seconds, overwrite page 0 of FILE (offset 0, 4096
//	                              bytes, one pwrite each, via os.File.WriteAt) with a page of one
//	                              repeated byte v (consecutive writes: consecutive values in
//	                              1..255); the source is a 4096-byte slot starting SKEW bytes into
//	                              page k of a POOLMIB-MiB heap pool (k = 0, 2, 4, ... cycling), so
//	                              the source's address % 4096 = SKEW and it crosses a page boundary
//	                              4096 - SKEW bytes in. The slots are filled once, before the loop
//	                              (records prepared earlier), or with "each" just before each write.
//	                              Never fsyncs.
//	tearw sync DIR N SECS         another process's writeback: sync_file_range(SYNC_FILE_RANGE_WRITE)
//	                              of page 0 of each DIR/f*, in a tight loop
package main

import (
	"fmt"
	"os"
	"strconv"
	"syscall"
	"time"
	"unsafe"
)

func main() {
	switch os.Args[1] {
	case "init":
		n, _ := strconv.Atoi(os.Args[3])
		for j := 0; j < n; j++ {
			f, err := os.OpenFile(fmt.Sprintf("%s/f%d", os.Args[2], j), os.O_RDWR|os.O_CREATE|os.O_TRUNC, 0o644)
			if err != nil {
				panic(err)
			}
			if _, err := f.WriteAt(make([]byte, 4096), 0); err != nil {
				panic(err)
			}
			if err := f.Sync(); err != nil {
				panic(err)
			}
			f.Close()
		}
	case "write":
		write()
	case "churn":
		churn()
	case "sync":
		n, _ := strconv.Atoi(os.Args[3])
		secs, _ := strconv.Atoi(os.Args[4])
		var fds []uintptr
		for j := 0; j < n; j++ {
			f, err := os.Open(fmt.Sprintf("%s/f%d", os.Args[2], j))
			if err != nil {
				panic(err)
			}
			fds = append(fds, f.Fd())
		}
		end := time.Now().Add(time.Duration(secs) * time.Second)
		calls := 0
		for time.Now().Before(end) {
			for _, fd := range fds {
				// SYNC_FILE_RANGE_WRITE = 2: start writeback of the dirty pages, do not wait
				if _, _, e := syscall.Syscall6(syscall.SYS_SYNC_FILE_RANGE, fd, 0, 4096, 2, 0, 0); e != 0 {
					panic(e)
				}
				calls++
			}
		}
		fmt.Printf("sync: %d sync_file_range calls\n", calls)
	}
}

// churn MIB SECS: another process's memory churn, the way an allocator returning memory does: an
// anonymous mapping of MIB MiB, touched, then in a loop every other page of it released
// (MADV_DONTNEED; odd pages, then even ones, alternately) and all touched again, so that free
// memory is fragmented into single pages and compaction has pages to move.
func churn() {
	mib, _ := strconv.Atoi(os.Args[2])
	secs, _ := strconv.Atoi(os.Args[3])
	m, err := syscall.Mmap(-1, 0, mib<<20, syscall.PROT_READ|syscall.PROT_WRITE, syscall.MAP_ANON|syscall.MAP_PRIVATE)
	if err != nil {
		panic(err)
	}
	for i := 0; i < len(m); i += 4096 {
		m[i] = 1
	}
	end := time.Now().Add(time.Duration(secs) * time.Second)
	rounds := 0
	for time.Now().Before(end) {
		ph := rounds & 1
		for i := ph * 4096; i < len(m); i += 8192 {
			if err := syscall.Madvise(m[i:i+4096], 4 /* MADV_DONTNEED */); err != nil {
				panic(err)
			}
		}
		for i := ph * 4096; i < len(m); i += 8192 {
			m[i] = 1
		}
		rounds++
	}
	fmt.Printf("churn: %d MiB, %d rounds\n", mib, rounds)
}

func write() {
	path := os.Args[2]
	skew, _ := strconv.Atoi(os.Args[3])
	secs, _ := strconv.Atoi(os.Args[4])
	poolMiB := 256
	if len(os.Args) > 5 {
		poolMiB, _ = strconv.Atoi(os.Args[5])
	}
	each := len(os.Args) > 6 && os.Args[6] == "each"
	f, err := os.OpenFile(path, os.O_RDWR, 0)
	if err != nil {
		panic(err)
	}
	pool := make([]byte, poolMiB<<20+8192)
	base := int((4096 - uintptr(unsafe.Pointer(&pool[0]))%4096) % 4096)
	pool = pool[base:]
	pages := (len(pool) - 8192) / 4096
	// slot k (k even) is the 4096 bytes at k*4096+skew; its value is (k/2) % 255 + 1, so that
	// consecutive writes write different values
	val := func(k int) byte { return byte((k/2)%255 + 1) }
	fill := func(k int) {
		src := pool[k*4096+skew : k*4096+skew+4096]
		src[0] = val(k)
		for m := 1; m < len(src); m *= 2 {
			copy(src[m:], src[:m])
		}
	}
	for k := 0; k < pages; k += 2 {
		fill(k)
	}
	end := time.Now().Add(time.Duration(secs) * time.Second)
	n := 0
	k := 0
	for ; ; k = (k + 2) % pages {
		if n%1024 == 0 && time.Now().After(end) {
			break
		}
		if each {
			fill(k)
		}
		if w, err := f.WriteAt(pool[k*4096+skew:k*4096+skew+4096], 0); err != nil || w != 4096 {
			panic(fmt.Sprint(w, err))
		}
		n++
	}
	fmt.Printf("write %s: skew %d (addr %% 4096 = %#x), fill %v: %d writes\n",
		path, skew, (uintptr(unsafe.Pointer(&pool[0]))+uintptr(skew))%4096, map[bool]string{true: "each", false: "once"}[each], n)
}

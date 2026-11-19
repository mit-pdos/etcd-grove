//go:build linux

package semantics

import (
	"os"

	"golang.org/x/sys/unix"
)

// mmap with no room left in the address space: the call does not return
// (2026-11-17, pending the user's review).
//
// Decision: a new mapping takes free cells of (0, maxAddr], page-aligned, as a
// Go allocation does (the Go heap and the mappings share the process's address
// space). From a heap that leaves no free range of the mapping's length, an
// mmap with arguments the model accepts may step to itself, changing nothing:
// the call does not return. This is how Perennial models a Go allocation with
// no free range (Lang.lean's AllocOOMS, AllocBytesOOMS; Perennial's
// docs/KNOWN_LIMITATIONS.md, "Out of memory is outside the model"): running
// out of address space is outside the model, and a proof covers the
// executions that do not. The failure with an errno stays an outcome of every
// mmap, ENOMEM included, room or not (Linux returns ENOMEM for want of address
// space, at the map count vm.max_map_count, and past RLIMIT_AS).
//
// Lean: Impl.lean: MmapRoom (the heap and the mappings leave room for len
// cells), MmapStall (the step to itself, a case of FsStep, which sees the heap;
// IsFsStep does not), FsStepV (the steps that return); the "Mmap" case of
// IsFsStep (success and any nonzero errno, unchanged). Specs.lean:
// wp_osMmapG (the stall handled by Löb induction, the file's OsMeta taken
// through an accessor opened at each step). Proof/os/CrashFile.lean: an
// operation of the extension is atomic only when it is not mmap (FsRetOp).
//
// Allowed: from a full address space, an mmap that never returns (as an
// allocation that never returns); an ENOMEM, from any state. Excluded: none
// of Linux's outcomes (ENOMEM is kept); the model adds the non-returning
// outcome, which a Go program on Linux reaches in its own way: the runtime
// ends it with "fatal error: out of memory" when its heap finds no room
// (runtime/malloc.go, throw("out of memory")), so no proof claims anything
// of an execution that runs out of address space.
//
// Why: the premise NoMapLockErr (premise_no_map_lock_err.go) excludes mmap's
// errors on covered files, ENOMEM included, so that bbolt's Open (its mmap)
// and a growing commit's remap return no error, where etcd's backend panics on
// one (backend.go: "cannot open database"). A premise on steps sees the
// extension's state, not the heap: from a state whose heap leaves no room, it
// must keep some step (StepKeeps), and with this decision the stall is that
// step. Without it, the premise could not exclude ENOMEM.
//
// Evidence: documented. mmap(2) (man-pages 6.9): "ENOMEM No memory is
// available. ENOMEM The process's maximum number of mappings would have been
// exceeded. ... ENOMEM (since Linux 4.7) The process's RLIMIT_DATA limit ...
// would have been exceeded"; Linux 7.0 mm/mmap.c, do_mmap: -ENOMEM when
// mm->map_count > sysctl_max_map_count, and get_unmapped_area's -ENOMEM when
// no gap fits (vm_unmapped_area). The non-returning outcome is assumed, as for
// Perennial's allocator: no measurement can show a call that does not return.
func MmapNoRoom(dir string) {
	f, _ := os.OpenFile(dir+"/db", os.O_RDWR|os.O_CREATE, 0o600)
	f.Truncate(1 << 16)
	var maps [][]byte
	for {
		b, err := unix.Mmap(int(f.Fd()), 0, 1<<16, unix.PROT_READ, unix.MAP_SHARED)
		if err == unix.ENOMEM {
			// Linux: at vm.max_map_count (65530 by default) or with no gap;
			// the model: an outcome of every mmap (and, under NoMapLockErr on
			// f's inode, excluded: there the call returns a mapping or, with no
			// room left in (0, maxAddr], never returns)
			break
		}
		if err != nil {
			panic(err)
		}
		maps = append(maps, b)
	}
	for _, b := range maps {
		unix.Munmap(b)
	}
	f.Close()
}

//go:build linux

package semantics

import (
	"os"
	"sort"
)

// (*os.File).Readdirnames(-1) returns at most 2^44 names (trusted model; a
// draft pending review, 2026-11-14).
//
// Decision: the model's read loop assumes, before each append, that the names
// read so far are fewer than 2^44 (Perennial's `assume`: the model diverges
// otherwise, as Perennial's `append` does on a length that overflows an int).
// Go never gets there without panicking: Readdirnames appends one name at a
// time (dir_unix.go's readdir: `names = append(names, string(name))`), and
// append panics with "growslice: len out of range" once the new capacity
// passes maxAlloc/16 = 2^44 strings (linux/amd64: maxAlloc = 2^48; a string
// header is 16 bytes), which it does before the length passes 2^44. The model
// excludes only executions in which Go panics in the runtime's allocator, the
// panic Perennial's slice models already treat as an assumption.
//
// Lean: LinuxFs/TrustedCode/os.lean: File.Readdirnames.impl (the `assume`).
//
// Excluded: a Readdirnames that returns more than 2^44 names.
//
// Why: documented (go1.27.3 src/runtime/slice.go, growslice: for a
// power-of-two element size, `overflow = uintptr(newcap) > (maxAlloc >>
// shift)`, then `if overflow || capmem > maxAlloc { panic(errorString(
// "growslice: len out of range")) }`; src/runtime/malloc.go: maxAlloc is
// 1<<heapAddrBits, 48 on linux/amd64) and measured (TestAppendStringsLenLimit:
// an append past 2^44 strings panics so, without allocating). Who needs it:
// fileutil.ReadDir sorts the names (sort.Strings, whose spec needs at most
// 2^62 of them: Go's heapSort computes 2*i+1, which overflows past 2^62).
func ReaddirnamesLen(d *os.File) {
	names, err := d.Readdirnames(-1)
	if err == nil {
		_ = len(names) <= 1<<44 // true
		sort.Strings(names)
	}
}

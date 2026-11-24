// The Go model of hash/crc32's Castagnoli arch hooks (crc32_amd64.go, Go 1.27.3, linux/amd64): the
// three declarations Code/hash/crc32.toml's [model] table replaces. Everything else of the package
// is Go's own: the translated code calls the hooks only as crc32.go's contract allows ("The
// interface that they implement": archInitCastagnoli only after archAvailableCastagnoli() returned
// true, archUpdateCastagnoli only after archInitCastagnoli(); castagnoliInitOnce, crc32.go:83-98,
// and update, which calls updateCastagnoli only once haveCastagnoli is set), and only the package
// calls them (they are unexported).

package crc32

import "internal/gomodel"

// MODEL: archAvailableCastagnoli is `return cpu.X86.HasSSE42` in Go, a property of the CPU that
// the runtime's cpuid assembly (internal/cpu's doinit, run by the runtime, not by package
// initialization) sets: no translated code determines it. The model answers gomodel.Choose(), any
// boolean at each call, so it covers every CPU (with or without SSE4.2, and the other
// architectures' crc32_otherarch.go, whose answer is false). Only castagnoliInitOnce calls it, once
// per process, so a per-call choice adds no behaviour Go lacks beyond a different CPU's.
func archAvailableCastagnoli() bool {
	return gomodel.Choose()
}

// MODEL: archInitCastagnoli is a no-op. Go's panics unless cpu.X86.HasSSE42, which the package's
// own code rules out (it calls this only after archAvailableCastagnoli() returned true), and
// otherwise fills castagnoliSSE42TableK1/K2 by calls of the SSE4.2 assembly castagnoliSSE42 on a
// zeroed stack buffer; only Go's archUpdateCastagnoli reads those two package variables. The
// model's archUpdateCastagnoli reads neither, so leaving them nil changes no result, and Go's
// version returns (it has no other effect and no failure).
func archInitCastagnoli() {}

// MODEL: archUpdateCastagnoli returns the CRC-32C of crc and p as Go's portable code computes it
// (simpleUpdate over simpleMakeTable(Castagnoli), crc32_generic.go). Go's computes it with SSE4.2
// CRC32 instructions in three streams combined through the K1/K2 tables (crc32_amd64.s); it panics
// unless cpu.X86.HasSSE42, which the package's code rules out (updateCastagnoli is set to it only
// after archAvailableCastagnoli() returned true). Both read p and write nothing the caller sees
// (the model's table is a fresh allocation). The trusted claim is that the assembly computes this
// function: Go's own TestArchCastagnoli (crc32_test.go) compares archUpdateCastagnoli with
// simpleUpdate over simpleMakeTable(Castagnoli) on every length up to and beyond its cutoffs.
func archUpdateCastagnoli(crc uint32, p []byte) uint32 {
	return simpleUpdate(crc, simpleMakeTable(Castagnoli), p)
}

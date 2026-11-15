//go:build linux

package semantics

import (
	"os"
)

// The target configuration C (environment assumption): the only machine the
// semantics claims to describe.
//
// Decision: Linux 7.0 on x86-64 with 4 KiB pages and no swap; one local ext4
// filesystem made by mkfs.ext4 with its defaults (4 KiB blocks, extents, a
// journal; no bigalloc, fast_commit, casefold, inline_data), mounted with
// ext4's default options (data=ordered, delalloc, dioread_nolock, barriers;
// any commit= interval); the process's RLIMIT_FSIZE unlimited; Go 1.27.3.
// notes/axiom-review/fs-config/check.sh checks a machine against C, and every
// experiment makes its filesystem with fs-config/mkfs-mount.sh.
//
// Lean: Impl.lean's header, "Configuration C"; pageIn (4096-byte pages, which
// on C are the blocks).
//
// Why this one: it is a reasonable etcd deployment (etcd's hardware guide
// recommends local SSD storage; ext4 made and mounted with its defaults is the
// root filesystem of Ubuntu's and Debian's installers and of most cloud
// images; etcd needs no special mount option), and every claim of the
// semantics is tested or argued for it alone. What C fixes, the semantics
// relies on:
//   - 4 KiB blocks = pages: a page past the size has no block of its own
//     shared with the end (durable zeros, data_durable_zeros.go);
//   - dioread_nolock: a new block may come back zeros under its size
//     (measured); data=ordered: never stale bytes;
//   - RLIMIT_FSIZE unlimited: a write is not cut short by the limit (Go's
//     WriteAt would retry into EFBIG; measured outside C with ulimit -f 6,
//     fs-v2-r4.md N2);
//   - no swap (an etcd deployment's usual setting; nothing in the model
//     depends on it now that tears are byte-level).
//
// Outside C (xfs, data=journal, 1-2 KiB blocks, other kernels): not
// described until tested on their own.
func Config(dir string) {
	f, _ := os.Create(dir + "/f")
	// on C: f is on ext4 with 4 KiB blocks, mounted with default options
	f.Close()
}

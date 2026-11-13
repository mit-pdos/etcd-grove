/-
Trust boundary: `os.Rename` (an axiom; see `Spec/os/Rename.lean`). D22 S-f, 2026-10-19;
`notes/decisions.md`, "D22 S-f carried out".
-/
module

public import Spec.os.Rename

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **Trust boundary** (D22 S-f). Since the merge onto the per-byte file extension, `os.Rename` is
no longer names-only: it sits beside a model, `TrustedCode/os.lean`'s `Rename.impl` (the
extension's `CallBegin`/`LstatDir`/`Rename`), from which walfs proves its renames. This axiom's
pre and post are the etcd backend's vocabulary (`fileHolds`, `pathOwn`), with no file-extension
resource, so the two do not connect: **until this axiom is replaced by a proof from `Rename.impl`
(when etcd's server moves onto the extension, with `fileHolds`/`pathOwn` defined over its tree),
no theorem may take `pathOwn` together with `osInv`** (`notes/STATUS.md`, "Known limitations";
`notes/axiom-review/fs-lean-merge.md`, finding 1). What it says: the POSIX `rename` system call, which Go's `os.Rename` makes
(after checking that `dst` is not a directory), is atomic: it either moves the directory entry
`src` to `dst`, replacing `dst`'s (a process that has the replaced file open keeps it: the old
backend's bbolt database is unaffected), or fails and changes nothing; Go then returns a
`*os.LinkError`, whose `Error()` returns a string. The file's contents do not change. The
program owning `dst` (`pathOwn`) is the data directory's closed-world assumption. What would
discharge it: a model of the file system (directory entries and inodes) under which `fileHolds`
is a points-to of a path. -/
axiom os.Rename.wp_proof : os.Rename.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial

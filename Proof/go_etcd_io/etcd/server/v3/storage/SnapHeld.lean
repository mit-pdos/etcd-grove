/-
**A received snapshot's database file, taken from the snapshot directory to be opened** (wal-link L2,
T1, decided by etcd-grove-03, 2026-11-17; `notes/axiom-review/releasesnapdbs.md`). Lean-first.

`snapHeld p D R'` is the file at `p` holding `D` (`backend.fileAt`, the claim on its name with the
file: lean's S5, merged 2026-11-19; until then `fileHolds`) together with the taker's resource `R'`,
sealed: the
directory's take (`snapDir_take`, `Proof/.../rafthttp/Net.lean`) makes it, and only
`OpenSnapshotBackend`'s proof opens it (it imports this module with `import all`), after its rename
moved the file onto the backend's path. While the token exists nobody holds the file's `fileAt`
at its directory path, and the taker's `R'` (from which the taker could make the directory's removal
fact of the file, e.g. the server's removal counter's authority) is locked in it: so no
`ReleaseSnapDBs`/`Release` caller holds that removal fact, and Go, which removes by listing the
directory, does not remove the held file (the refutation of 2026-11-17: a held `fileHolds` framed
across a `ReleaseSnapDBs` above its index).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvSnapshot

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace storage

open Iris Iris.BI Iris.ProofMode

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **The snapshot file at `p` holding `D`, taken with the taker's `R'`** (sealed; see the file
header). -/
@[no_expose] def snapHeld (p : GoString) (D : backend.Data) (R' : IProp GF) : IProp GF :=
  iprop(backend.fileAt p D ∗ R')

/-- The token from its parts (the directory's take). Harmless to clients: it only seals. -/
theorem snapHeld_intro (p : GoString) (D : backend.Data) (R' : IProp GF) :
    backend.fileAt p D ∗ R' ⊢ snapHeld p D R' := by
  unfold snapHeld; exact .rfl

end defs

end storage
end EtcdGrove
end Perennial

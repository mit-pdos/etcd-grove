/-
**The snapshotter** (`etcdserver/api/snap`, names only; D22 S-f, 2026-10-19): the vocabulary of
its trust-boundary specs. Lean-first (no Rocq counterpart).

* `isSnapshotter ss` (persistent): `ss` is a `*snap.Snapshotter` (`snap.New(lg, dir)`: its fields,
  the logger and the snapshot directory, set once and read-only after). An opaque predicate
  (`snapshotterRO`) made persistent by its definition: the snapshotter's fields are not modeled.
* `snapDBPath ss id` (opaque): the path of the database snapshot of index `id` in `ss`'s
  directory (`ss.dbFilePath(id)`: `<dir>/<id as 16 hex digits>.snap.db`). `DBFilePath` returns
  it (`Spec/.../snap/Snapshotter__DBFilePath.lean`); the transport's `SaveDBFrom` writes the file
  there (D22 S-i).
-/
module

public import Perennial.Proof.ProofPrelude
public import Perennial.Golang.Theory

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace snap

open Iris Iris.BI

/-- **The path of the database snapshot of index `id`** of the snapshotter `ss` (opaque; see the
file header). -/
opaque snapDBPath [FfiSyntax] (ss : Loc) (id : w64) : GoString

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `ss`'s fields, read-only (opaque; see the file header). -/
opaque snapshotterRO (ss : Loc) : IProp GF

/-- **`ss` is a snapshotter** (persistent; see the file header). -/
def isSnapshotter (ss : Loc) : IProp GF := iprop(□ snapshotterRO ss)

instance isSnapshotter_persistent (ss : Loc) : Persistent (isSnapshotter (GF := GF) ss) := by
  unfold isSnapshotter; infer_instance

end defs

end snap
end EtcdGrove
end Perennial

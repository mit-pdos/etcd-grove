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
* `msgIs m ml rc` (persistent; D22 S-i): `m` is a `*snap.Message` (`snap.NewMessage(ml, rc,
  size)`: the raft message `ml`, the reader `rc` wrapped in an exact-size reader, the total size
  and the one-slot `closeC` channel), its fields read-only for good (`NewMessage` writes them
  once; `CloseWithError` reads the reader and sends on `closeC`, `CloseNotify` reads `closeC`). An
  opaque predicate (`msgRO`): `snap.Message` is an axiomatized type, so its fields are not
  modeled. `NewMessage`'s spec makes it (D22 S-h); the transport's `SendSnapshot` takes it.
* `msgCloseC m c` (persistent; D22 S-h): `m`'s `closeC` is the channel `c` (`NewMessage`'s
  `make(chan bool, 1)`, read by `CloseNotify`). An opaque predicate (`msgCloseRO`), as `msgRO`.
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
opaque snapDBPath [GooseExts] (ss : Loc) (id : w64) : GoString

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `ss`'s fields, read-only (opaque; see the file header). -/
opaque snapshotterRO (ss : Loc) : IProp GF

/-- **`ss` is a snapshotter** (persistent; see the file header). -/
def isSnapshotter (ss : Loc) : IProp GF := iprop(□ snapshotterRO ss)

/-- **The snapshotter `ss`'s directory reads** (opaque, a named premise about the program's
environment; D22 receiver epochs, S8d, 2026-10-24): listing `ss`'s directory does not fail
(`DBFilePath`'s `fileutil.ReadDir`), and a `.snap.db` file the program holds there is found. The
premise excluding the failure is `storage.snapOpensOk`. -/
opaque dirReadOk (ss : Loc) : Prop

instance isSnapshotter_persistent (ss : Loc) : Persistent (isSnapshotter (GF := GF) ss) := by
  unfold isSnapshotter; infer_instance

/-- `m`'s fields, read-only (opaque; see the file header). -/
opaque msgRO (m ml : Loc) (rc : GoInterface) : IProp GF

/-- **`m` is a `*snap.Message` of the raft message `ml` and the reader `rc`** (persistent; see the
file header). -/
def msgIs (m ml : Loc) (rc : GoInterface) : IProp GF := iprop(□ msgRO m ml rc)

instance msgIs_persistent (m ml : Loc) (rc : GoInterface) :
    Persistent (msgIs (GF := GF) m ml rc) := by
  unfold msgIs; infer_instance

/-- `m`'s `closeC` field, read-only (opaque; see the file header). -/
opaque msgCloseRO (m c : Loc) : IProp GF

/-- **`m`'s `closeC` is `c`** (persistent; D22 S-h; see the file header). -/
def msgCloseC (m c : Loc) : IProp GF := iprop(□ msgCloseRO m c)

instance msgCloseC_persistent (m c : Loc) : Persistent (msgCloseC (GF := GF) m c) := by
  unfold msgCloseC; infer_instance

end defs

end snap
end EtcdGrove
end Perennial

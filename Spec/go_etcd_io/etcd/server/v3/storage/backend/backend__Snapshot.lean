/-
## `(*backend).Snapshot()` (`backend.go:360-423`): trusted (names only)

**Users.** 2d's merged snapshot (`snapshot_merge.go:37`, after `KV().Commit()`), the maintenance
server's `Snapshot` (`v3rpc/maintenance.go:146`, 2a). Snippet `snapshot.go` (`ReqSnapshotStream`).

**Why it is true.** `b.batchTx.Commit()` (the commit protocol, as `ForceCommit`); `b.mu.RLock()`;
bbolt's `Begin(false)` (4c: a read transaction at the committed data, the reader slot lent to
`mmaplock`; a failure is `lg.Fatal`, which never returns): the snapshot is of the image of the last
commit at that point, which is in the history (`beCommitted`); `tx.Size()` and a monitor goroutine
(its ticker's period at least `minSnapshotWarningTimeout`, so `NewTicker` does not panic; a thread
from `envOk`'s pool) that only logs, until `Close` stops it. `beSnap γ s I bs` holds the bbolt read
transaction (`boltTx` at `ro D`, `imgOf D = I`), the slot, the channels; `bs` is what `WriteTo`
writes (4c's `Tx.WriteTo`).

**Changes** (from `specs-ref`'s `backend__Snapshot.lean`, D22's `bkSnapAt`): the image is a committed
one by the client-owned history (`beCommitted`, read with `beHist_mem`), not an observation fired
under the batch lock: a commit may land between `Commit()` and `Begin` (mvcc's compaction batches
commit on their own), so the image is the last commit's at `Begin`, which no caller's update can
pin. A reader slot (bbolt's), not a thread token.

**Margin.** The image is the last commit's at the `Begin` (the post says only "a committed one").
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.backend.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Backend

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

/-- **`b.Snapshot()`**: a snapshot of a committed image `I` (in the client's history), with its file
bytes `bs`. -/
def backend.Snapshot.spec : Prop :=
  ∀ (γ : BeNames) (b : Loc) (p : GoString) (Pk : IProp GF) (q : Qp),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ isBackend γ b p Pk ∗ beOpen γ q ∗ beRdToks γ 1 }}
    (App (Val (b @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty @!! go!"Snapshot")) (Val #()))
  {{ (r : GoInterface), RET #r; ∃ (s : Loc) (I : Image) (bs : List w8),
      ⌜r = interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.snapshot.ty) #s ∧ imgBytes I bs⌝ ∗ beSnap γ s I bs ∗ beCommitted γ I ∗
      beOpen γ q }}

end spec

end Backend
end EtcdGrove
end Perennial

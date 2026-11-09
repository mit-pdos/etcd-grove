/-
## `(*backend).Snapshot()` (`backend.go:360-423`): trusted (names only)

**Users.** 2d's merged snapshot (`snapshot_merge.go:37`, after `KV().Commit()`), the maintenance
server's `Snapshot` (`v3rpc/maintenance.go:146`, 2a). Snippet `snapshot.go` (`ReqSnapshotStream`).

**Why it is true.** `b.batchTx.Commit()` (the commit protocol, as `ForceCommit`); `b.mu.RLock()`;
bbolt's `Begin(false)` (4c: a read transaction at the committed data, the reader slot lent to
`mmaplock`; a failure is `lg.Fatal`, which never returns): the snapshot is of the image of the last
commit at that point, which is in the history (`beCommitted`); `tx.Size()` and a monitor goroutine
(its ticker's period at least `minSnapshotWarningTimeout`, so `NewTicker` does not panic; a thread
from `envOk`'s pool) that only logs, until `Close` stops it. `beSnapN γ s I n` holds the bbolt read
transaction (`boltTx` at `ro D`, `imgOf D = I`), the slot, the channels; `n` is `tx.Size()`, the length of
every `WriteTo`'s bytes (4c's `Tx.WriteTo`).

**The lower bound** (verify-round, A10-completeness F1): the caller names a prefix `L0` of the
history (`beHistLb`, from its own `beHist` by `beHist_lb`); the image is the last of an extension of
`L0`. True: `Snapshot`'s own `Commit()` takes the batch lock, which waits for every commit of `L0`
(commits run under it) to have written its meta page; so the file's last completed commit, which
`Begin(false)` reads, is `L0`'s last or a later one (the history may already hold a later attempt
not yet written, which the post's extension simply leaves out: `beHistLb_mono`). 2d's merged snapshot
(`snapshot_merge.go:36-37`: `KV().Commit()`, then `Snapshot()`) takes `L0` after its commit, so the
image is at least the state machine at the applied index.

**The size** (verify-round, A11-completeness F5): `beSnapN γ s I n` carries the size only; each
`WriteTo` writes some bytes of `I` of that length (bbolt's `Tx.WriteTo` gives a fresh image of the
transaction's size on each call).

**Changes** (from `specs-ref`'s `backend__Snapshot.lean`, D22's `bkSnapAt`): the image is a committed
one by the client-owned history (`beCommitted`, read with `beHist_mem`), not an observation fired
under the batch lock: a commit may land between `Commit()` and `Begin` (mvcc's compaction batches
commit on their own), so the image is the last commit's at `Begin`, which no caller's update can
pin. A reader slot (bbolt's), not a thread token.

**Margin.** The image is the last completed commit's at the `Begin`; the post says only that it
extends the caller's `L0` (an image no older than `L0`'s last), not that nothing later completed.
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

/-- **`b.Snapshot()`**: a snapshot of a committed image `I` (in the client's history), no older than
the last of the caller's prefix `L0` (the last of an extension of it), of size `n`. -/
def backend.Snapshot.spec : Prop :=
  ∀ (γ : BeNames) (b : Loc) (p : GoString) (Pk : IProp GF) (q : Qp) (L0 : List Image),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ isBackend γ b p Pk ∗ beOpen γ q ∗ beRdToks γ 1 ∗
      beHistLb γ L0 }}
    (App (Val (b @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty @!! go!"Snapshot")) (Val #()))
  {{ (r : GoInterface), RET #r; ∃ (s : Loc) (I : Image) (n : Nat) (L1 : List Image),
      ⌜r = interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.snapshot.ty) #s ∧
        n < 2 ^ 48 ∧ (L0 ++ L1).getLast? = some I⌝ ∗
      beSnapN γ s I n ∗ beCommitted γ I ∗ beHistLb γ (L0 ++ L1) ∗ beOpen γ q }}

end spec

end Backend
end EtcdGrove
end Perennial

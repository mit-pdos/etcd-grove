/-
## `(*batchTxBuffered).UnsafeDelete(bucket, key)` (`batch_tx.go:412-415`): translated

**Users.** mvcc's compaction (`kvstore_compaction.go:62`, `Key`, a safe-range bucket), the lessor's
revoke (`schema/lease.go`, `lessor.go:359`, under mvcc's session), the schema's deletes
(`auth_users.go:49`, `auth_roles.go:65`, `alarm.go:81`, `membership.go`, `version.go:66`,
`actions.go:48`). Snippet `parts.go` (`ReqDeleteVisible`, `ReqLentWrite`).

**Proof sketch.** `batchTx.UnsafeDelete` (bbolt's `Delete` on the write transaction: the batch
image without `k`; `pending++`; a missing bucket or an error is `lg.Fatal`), then
`pendingDeleteOperations++` (so `Unlock` commits: the readers see the delete at the commit, the
second update). A safe-range bucket's delete holds the safe-range lock, so no non-blocking
defragmentation copies the key back.

**Changes** (from `specs-ref`'s `thinV`/`DelKeys`): an exact delete of the batch image; the
safe-range lock (new in the pinned code).

**Margin.** None.
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

/-- **`t.UnsafeDelete(bk, k)`**: the batch image without `k` in `bk`'s bucket. -/
def batchTxBuffered.UnsafeDelete.spec : Prop :=
  ∀ (γ : BeNames) (q : Qp) (F : Fp) (S : Sess) (G : Fp) (C : Image) (bk : GoInterface)
    (bi : BktInfo) (ks : GoSlice) (dk : DFrac) (k : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ beSess γ q F S ∗ bucketOk bk bi ∗ beCur γ G C ∗ ⌜G (.key bi.name k)⌝ ∗
      writable γ F (Fp.key bi.name k) ∗ (if bi.safe then beDelHeld γ else iprop(True)) ∗
      ks ↦*{dk} k }}
    (App (App (Val ((btLoc γ) @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.batchTxBuffered.ty @!! go!"UnsafeDelete")) (Val #bk)) (Val #ks))
  {{ RET #(); beSess γ q F (S.del bi.name k) ∗ beCur γ G (C.del bi.name k) ∗
      (if bi.safe then beDelHeld γ else iprop(True)) ∗ ks ↦*{dk} k }}

end spec

end Backend
end EtcdGrove
end Perennial

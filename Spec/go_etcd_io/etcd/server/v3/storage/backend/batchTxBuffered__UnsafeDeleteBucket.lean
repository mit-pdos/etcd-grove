/-
## `(*batchTxBuffered).UnsafeDeleteBucket(bucket)` (`batch_tx.go:417-420`): translated

**Users.** The schema's `TrimClusterFromBackend` (`membership.go:69`, the `cluster` bucket).

**Proof sketch.** `batchTx.UnsafeDeleteBucket` (bbolt's `DeleteBucket`; `ErrBucketNotFound`
ignored; other errors `lg.Fatal`), `pending++`, `pendingDeleteOperations++` (the readers see it at
the commit). The caller owns the whole bucket.

**Changes.** From `specs-ref`'s: over the bucket's footprint. **Margin.** None.
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

/-- **`t.UnsafeDeleteBucket(bk)`**: `bk`'s bucket gone from the batch image, entries and all. -/
def batchTxBuffered.UnsafeDeleteBucket.spec : Prop :=
  ∀ (γ : BeNames) (q : Qp) (F : Fp) (S : Sess) (G : Fp) (C : Image) (bk : GoInterface)
    (bi : BktInfo),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ beSess γ q F S ∗ bucketOk bk bi ∗ beCur γ G C ∗ ⌜∀ c, Fp.bucket bi.name c → G c⌝ ∗
      writable γ F (Fp.bucket bi.name) ∗ (if bi.safe then beDelHeld γ else iprop(True)) }}
    (App (Val ((btLoc γ) @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.batchTxBuffered.ty @!! go!"UnsafeDeleteBucket")) (Val #bk))
  {{ RET #(); beSess γ q F (S.dropBkt bi.name) ∗ beCur γ G (C.dropBkt bi.name) ∗
      (if bi.safe then beDelHeld γ else iprop(True)) }}

end spec

end Backend
end EtcdGrove
end Perennial

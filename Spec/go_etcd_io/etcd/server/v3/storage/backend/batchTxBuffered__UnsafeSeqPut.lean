/-
## `(*batchTxBuffered).UnsafeSeqPut(bucket, key, value)` (`batch_tx.go:407-410`): translated

**Users.** mvcc's puts and tombstones (`kvstore_txn.go:259, 323`). Snippet `ranges.go`
(`ReqSeqRange`).

**Proof sketch.** `batchTx.UnsafeSeqPut` (`unsafePut` with the fill percent at `0.9`), then the
write buffer's `putSeq` (`verify.Verify` off by `envOk`; the bucket's sequential flag kept: the
write-back neither sorts nor deduplicates it, so the key must be above every key of the bucket the
read buffer may hold, `Sess.fresh`, in any bucket).

**Changes** (from `specs-ref`'s): `Sess.fresh` in place of the old `P.SB` premise. **Margin.** None.
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

/-- **`t.UnsafeSeqPut(bk, k, v)`**: as `UnsafePut`, for a key above every key of the bucket. -/
def batchTxBuffered.UnsafeSeqPut.spec : Prop :=
  ∀ (γ : BeNames) (q : Qp) (F : Fp) (S : Sess) (G : Fp) (C : Image) (bk : GoInterface)
    (bi : BktInfo) (ks vs : GoSlice) (k v : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ beSess γ q F S ∗ bucketOk bk bi ∗ beCur γ G C ∗ ⌜G (.key bi.name k)⌝ ∗
      writable γ F (Fp.key bi.name k) ∗ ⌜S.fresh bi.name k⌝ ∗
      ⌜k.length + v.length ≤ Bbolt.bboltEntryMax⌝ ∗ ks ↦*□ k ∗ vs ↦*□ v }}
    (App (App (App (Val ((btLoc γ) @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.batchTxBuffered.ty @!! go!"UnsafeSeqPut")) (Val #bk)) (Val #ks)) (Val #vs))
  {{ RET #(); beSess γ q F (S.put bi.name k v) ∗ beCur γ G (C.put bi.name k v) }}

end spec

end Backend
end EtcdGrove
end Perennial

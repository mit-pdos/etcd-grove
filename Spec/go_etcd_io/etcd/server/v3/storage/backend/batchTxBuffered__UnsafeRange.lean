/-
## `(*batchTxBuffered).UnsafeRange(bucket, key, endKey, limit)` (promoted `batchTx.UnsafeRange`, `batch_tx.go:193-204`): translated

**Users.** mvcc's compaction (`kvstore_compaction.go:58`), the schema's reads on the batch
transaction (4b: lease, membership, auth `Get*` under the writer's lock, the version, the
consistent index in the hooks' tests). Snippet `ranges.go`.

**Proof sketch.** `t.tx.Bucket(name)` (nil: `lg.Fatal`), `unsafeRange` over bbolt's cursor of the
write transaction (4c's `Cursor.Seek`/`Next`: the batch image's bucket in key order; an empty end
the key alone, else cut at a positive limit). The slices are bbolt's: lent while the session lives
(4c's `txBytes`), back for the session (`rangeRes`).

**Changes** (from `specs-ref`'s): over the session; the bytes lent (round 1, T3). **Margin.** None.
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

/-- **`t.UnsafeRange(bk, k, e, limit)`**: the batch image's range (`btRange`). -/
def batchTxBuffered.UnsafeRange.spec : Prop :=
  ∀ (γ : BeNames) (q : Qp) (F : Fp) (S : Sess) (bk : GoInterface) (bi : BktInfo)
    (ks es : GoSlice) (dk de : DFrac) (k e : GoString) (limit : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ beSess γ q F S ∗ bkt γ bk bi ∗ ks ↦*{dk} k ∗ es ↦*{de} e }}
    (App (App (App (App (Val ((btLoc γ) @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.batchTxBuffered.ty @!! go!"UnsafeRange")) (Val #bk)) (Val #ks))
      (Val #es)) (Val #limit))
  {{ (kl vl : GoSlice), RET (PairV #kl #vl); ks ↦*{dk} k ∗ es ↦*{de} e ∗
      ∃ l, ⌜btRange (S.cur.ents bi.name) k e (sint.Z limit) l⌝ ∗ rangeRes kl vl l (beSess γ q F S) }}

end spec

end Backend
end EtcdGrove
end Perennial

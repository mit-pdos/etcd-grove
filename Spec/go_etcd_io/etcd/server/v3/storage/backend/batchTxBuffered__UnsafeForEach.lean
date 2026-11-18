/-
`UnsafeForEach` (the backend). `t.UnsafeForEach(bucket, visitor)` under the lock, on a bucket the
writer's contents hold empty: the visitor is not called and `nil` is returned. Lean-first (no Rocq
counterpart); the authstore-noax stage (2026-11-18, `notes/decisions.md`, "authstore-noax"): what
`NewAuthStore`'s `refreshRangePermCache` needs of its batch transaction (schema's
`unsafeGetAllUsers` over the users' bucket, empty at the store's construction).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvBackend

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.backend backend

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

/-- `t.UnsafeForEach(bucket, visitor)` under the lock at the state `st`, on a bucket of the table
whose contents in the writer's contents are empty (absent or with no key: `bktOf st.S bi.name = ∅`):
`nil`, the visitor never called, the lock's state unchanged. Only the empty case (the general
spec, the visitor over the bucket's entries in key order, is the spec plan's
`SpecPlan/Spec/go_etcd_io/etcd/server/v3/storage/backend/batchTxBuffered__UnsafeForEach.lean`).

Go (`batch_tx.go:250-259` at the etcd pin): the promoted `batchTx.UnsafeForEach` is
`unsafeForEach(t.tx, bucket, visitor)`: `t.tx.Bucket(bucket.Name())`, bbolt's writer transaction
(the session's writes included: the writer's contents `st.S`, as `UnsafeRange` reads them,
`batchTxBuffered.UnsafeRange.spec`); a nil bucket (absent) returns `nil`; else
`b.ForEach(visitor)` (`bbolt@v1.5.0/bucket.go:390-402`): `c.First()` on an empty bucket returns a
nil key, so the loop body (the visitor) never runs and `ForEach` returns `nil` (the transaction is
open while the lock is held, `b.tx.db != nil`). Nothing is written. -/
abbrev backend.batchTxBuffered.UnsafeForEach.spec : Prop :=
  ∀ (γ : BNames) (P : BParams) (W Pk : IProp GF) (b : Loc) (t : Loc) (st : BSess) (bk : GoInterface)
    (bi : BucketInfo) (vis : GoFunc),
  P.has bi → bktOf st.S bi.name = ∅ →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ isBackend γ P W Pk b ∗
      bF go!"batchTx" b ↦□ t ∗ batchLocked γ P b st ∗ isBucket bk bi }}
    (App (App (Val (t @!! go.GoType.PointerType batchTxBuffered.ty @!! go!"UnsafeForEach")) (Val #bk))
      (Val #vis))
  {{ (err : GoInterface), RET #err; ⌜err = GoInterface.nil⌝ ∗ batchLocked γ P b st }}

end spec

end EtcdGrove
end Perennial

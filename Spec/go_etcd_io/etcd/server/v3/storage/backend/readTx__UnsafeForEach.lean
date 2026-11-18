/-
`UnsafeForEach` (the backend). `rt.UnsafeForEach(bucket, visitor)` of the held shared read
transaction, on a bucket its readers' view holds empty: the visitor is not called and `nil` is
returned. Lean-first (no Rocq counterpart); the authstore-noax stage (2026-11-18,
`notes/decisions.md`, "authstore-noax"): what the auth store's `Recover` (its
`refreshRangePermCache`, schema's `unsafeGetAllUsers`) needs of a new backend's read transaction.
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

/-- `rt.UnsafeForEach(bucket, visitor)` of the held shared read transaction (any share `p` of
bbolt's transaction, as `readTx.UnsafeRange.spec`), on a bucket of the table whose readers' view is
empty (`vOf P rv bi.name k = none` at every key: no entry in the read buffer's bucket, none in the
interval's committed data): `nil`, the visitor never called, the held read unchanged. Only the
empty case (the general spec is the spec plan's
`SpecPlan/Spec/go_etcd_io/etcd/server/v3/storage/backend/readTx__UnsafeForEach.lean`).

Go (`read_tx.go:61-83` at the etcd pin): the promoted `baseReadTx.UnsafeForEach` runs
`baseReadTx.buf.ForEach(bucket, getDups)` over the read buffer's bucket (no entry: a buffered
entry would be the view's value at its key), then, under `txMu`, `unsafeForEach(baseReadTx.tx,
bucket, visitNoDup)` over bbolt's read transaction, the interval's committed data (an absent
bucket returns `nil`; an empty one's `ForEach` runs no iteration, `bbolt@v1.5.0/bucket.go:390-402`),
then `buf.ForEach(bucket, visitor)` (no entry): the visitor never runs and each step returns
`nil`. -/
abbrev backend.readTx.UnsafeForEach.spec : Prop :=
  ∀ (γ : BNames) (P : BParams) (W Pk : IProp GF) (b : Loc) (rt : Loc) (rtx : Loc) (rv : RView)
    (p : Qp) (bk : GoInterface) (bi : BucketInfo) (vis : GoFunc),
  P.has bi → (∀ k, vOf P rv bi.name k = none) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ isBackend γ P W Pk b ∗
      bF go!"readTx" b ↦□ rt ∗ rtHeldF γ P b rtx rv p ∗ isBucket bk bi }}
    (App (App (Val (rt @!! go.GoType.PointerType readTx.ty @!! go!"UnsafeForEach")) (Val #bk))
      (Val #vis))
  {{ (err : GoInterface), RET #err; ⌜err = GoInterface.nil⌝ ∗ rtHeldF γ P b rtx rv p }}

end spec

end EtcdGrove
end Perennial

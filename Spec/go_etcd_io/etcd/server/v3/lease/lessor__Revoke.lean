/-
`(*lessor).Revoke` (`server/lease/lessor.go`). Lean-first (no Rocq counterpart); see
`Proof/go_etcd_io/etcd/server/v3/lease/InvLessor.lean`, `notes/leases-plan.md` (L2). Over mvcc's
API (strict M1, 2026-11-05): `notes/mvcc-api-clients/ServerSpecs.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.lease.LessorBackend
public import Proof.go_etcd_io.etcd.server.v3.lease.MvccShapes

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc mvcc.api srvApi

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.lease.Assumptions]
variable [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- **`le.Revoke(id)`** (strict M1, 2026-11-05: the frozen draft's `lessor.Revoke.specA`,
`notes/mvcc-api-clients/ServerSpecs.lean` §5, over mvcc's API; xreview §3): one update, the deleter's `Write`'s begin at `σ₀`
whose payload is the end updates of exactly the lease's deletions (`auBegin γ σ₀ (auEnd γ σ₀ dels
Y)`: the builders' continuation form; the writer's half is exclusive, so the two cannot be built
apart). `rd ≠ nil` is `mvccDeleter`'s (round 15). The sort's premise `(stateAfter σ₀.log).length ≤
2 ^ 62` stays a premise, which the caller now derives from the writer's receipt (`⧖ (logCh σ₀.log)`,
the writer's facts; a live key-value is a change, `receiptBound ≤ 2 ^ 48`; the tester from its keys).
* `id` not live: `ErrLeaseNotFound`, the update and `Pre` back;
* `id` live: `Y`, `Post`, the lease's record deleted, `id` out of the live set.
The proof: `rd()` by `mvccDeleter` (its update this one), the deletes by `Txn.DeleteRange`
(`shapes.law`), the record's delete by `mvccTxn_leaseDelete.law` (which gives `End`'s triple, not
`mvccTxn`: the backend's batch session admits only `Unlock` after an `UnsafeDelete`), `End`'s triple
with `P` from the hook's `Q` (`csContractA`) and the nested end update. -/
abbrev lease.lessor.Revoke.spec : Prop :=
  ∀ (lp : Loc) (γ : MvccName) (id : w64) (rd : GoFunc) (q : Qp) (B : BkRef) (P : IProp GF)
    (f : GoFunc) (σ₀ : MvccState) (L : List w64) (r : GMap GoString backend.BktData)
    (Pre Q Post Y : IProp GF),
  let γl := mvccLeases γ
  let dels := mvcc.leaseDels (mvcc.stateAfter σ₀.log) id
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      lease.lessorInv lp γl ∗ threadTok ∗ lease.rdOwn γl rd ∗ mvccDeleter rd γ ∗
      mvccBackend γ q B P ∗ hookIs B f ∗ csContractA P f Pre Q Post ∗
      ⌜σ₀.pending = none ∧ (mvcc.stateAfter σ₀.log).length ≤ 2 ^ 62⌝ ∗
      auBegin γ σ₀ (auEnd γ σ₀ dels Y) ∗
      lease.leaseOwn γl L (mvcc.leaseItemsOf (mvcc.stateAfter σ₀.log)) ∗ lease.leaseRevokers γl L ∗
      backend.rbPart B.γB (· = mvcc.leaseName) r ∗ ⌜mvcc.leaseParams B.P⌝ ∗ lease.lessorBeOn lp B.b }}
    (App (Val (lp @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.lease.lessor.ty
      @!! go!"Revoke")) (Val #id))
  {{ (err : GoInterface), RET #err; threadTok ∗ lease.rdOwn γl rd ∗ mvccBackend γ q B P ∗
      lease.lessorBeOn lp B.b ∗
      ((⌜id ∉ L⌝ ∗
          (∃ e : GoInterfaceOk, globalAddr go_etcd_io.etcd.server.v3.lease.ErrLeaseNotFound ↦□
            GoInterface.ok e ∗ ⌜err = GoInterface.ok e⌝) ∗
          auBegin γ σ₀ (auEnd γ σ₀ dels Y) ∗ Pre ∗
          lease.leaseOwn γl L (mvcc.leaseItemsOf (mvcc.stateAfter σ₀.log)) ∗ lease.leaseRevokers γl L ∗
          backend.rbPart B.γB (· = mvcc.leaseName) r) ∨
       (⌜id ∈ L ∧ err = GoInterface.nil⌝ ∗ Y ∗ Post ∗
          lease.leaseOwn γl (L.filter (· != id))
            (mvcc.leaseItemsOf (mvcc.stateAfter (mvcc.commitLog σ₀.log dels))) ∗
          lease.leaseRevokers γl (L.filter (· != id)) ∗
          backend.rbPart B.γB (· = mvcc.leaseName)
            (mvcc.rbDel r mvcc.leaseName (u64Le id).reverse))) }}

end spec

end EtcdGrove
end Perennial

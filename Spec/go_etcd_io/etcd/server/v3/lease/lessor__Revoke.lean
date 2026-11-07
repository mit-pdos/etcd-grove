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
* `id` not live: `ErrLeaseNotFound`, `Pre` back (no update taken);
* `id` live: `Y`, `Post`, the lease's record deleted, `id` out of the live set.
The proof: `rd()` by `mvccDeleter` (its update this one), the deletes by `Txn.DeleteRange`
(`shapes.law`), the record's delete by `mvccTxn_leaseDelete.law` (which gives `End`'s triple, not
`mvccTxn`: the backend's batch session admits only `Unlock` after an `UnsafeDelete`), `End`'s triple
with `P` from the hook's `Q` (`csContractA`) and the nested end update.
**The begin state's reachability** (decided by the coordinator, 2026-11-05; superseding the
draft's premise without it): `MvccReachable σ₀ ∧ σ₀.log.length + 3 ≤ 2 ^ 63`, which the deletes'
`delKeys` need (`txn.delKeys_eq`'s `LogOk`) and the API gives only through `mvccState_reachable.law`
(`isMvcc`, not held here); the server's caller has it from the writer's facts, the tester from
`mvccState_reachable.law`.
**The update only for a live lease** (decided by the coordinator, 2026-11-06; superseding the
draft's update taken always and given back in the not-live arm): `if decide (id ∈ L) then auBegin …
else True`, as txn's `Put` for a lease. The code returns `ErrLeaseNotFound` before `rd()`, and the
server's caller builds the update from its writer's half, which no law recovers from an unused
update (`notes/mvcc-migration/server.md`, "Found", third session, (2)).
**The lessor revocable** (`lease.lessorRevocable γl`: its history is not kept monotone; the
lease-grant plan's D2, 2026-11-02, from `lean`, merged 2026-11-06). -/
abbrev lease.lessor.Revoke.spec : Prop :=
  ∀ (lp : Loc) (γ : MvccName) (id : w64) (rd : GoFunc) (q : Qp) (B : mvcc.KBReal) (P : IProp GF)
    (f : GoFunc) (σ₀ : MvccState) (L : List w64) (r : GMap GoString backend.BktData)
    (Pre Q Post Y : IProp GF),
  let γl := mvccLeases γ
  let dels := mvcc.leaseDels (mvcc.stateAfter σ₀.log) id
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      lease.lessorInv lp γl ∗ lease.lessorRevocable γl ∗ threadTok ∗ mvccReaders γ 1 ∗
      lease.rdOwn γl rd ∗ mvccDeleter rd γ ∗
      mvccBackend γ q B P ∗ hookIs B f ∗ csContractA P f Pre Q Post ∗
      ⌜σ₀.pending = none ∧ (mvcc.stateAfter σ₀.log).length ≤ 2 ^ 62 ∧
        MvccReachable σ₀ ∧ σ₀.log.length + 3 ≤ 2 ^ 63⌝ ∗
      (if decide (id ∈ L) then auBegin γ σ₀ (auEnd γ σ₀ dels Y) else iprop(True)) ∗
      lease.leaseOwn γl L (mvcc.leaseItemsOf (mvcc.stateAfter σ₀.log)) ∗ lease.leaseRevokers γl L ∗
      backend.rbPart B.γB (· = mvcc.leaseName) r ∗ ⌜mvcc.leaseParams B.P⌝ ∗ lease.lessorBeOn lp B.be }}
    (App (Val (lp @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.lease.lessor.ty
      @!! go!"Revoke")) (Val #id))
  {{ (err : GoInterface), RET #err; threadTok ∗ mvccReaders γ 1 ∗ lease.rdOwn γl rd ∗
      mvccBackend γ q B P ∗
      lease.lessorBeOn lp B.be ∗
      ((⌜id ∉ L⌝ ∗
          (∃ e : GoInterfaceOk, globalAddr go_etcd_io.etcd.server.v3.lease.ErrLeaseNotFound ↦□
            GoInterface.ok e ∗ ⌜err = GoInterface.ok e⌝) ∗
          Pre ∗
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

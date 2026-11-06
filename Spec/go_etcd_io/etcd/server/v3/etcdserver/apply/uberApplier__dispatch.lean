/-
`apply.uberApplier.dispatch` (uber_applier.go). Lean-first (no Rocq counterpart); the vocabulary is
`Proof/go_etcd_io/etcd/server/v3/etcdserver/apply/InvUber.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.InvUber

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver.apply go_etcd_io.etcd.api.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]

/-- **`a.dispatch(r, shouldApplyV3)`**, the `applyFunc` `uberApplier.Apply` hands the chain's
`Apply` (`a.dispatch`, a method value): under the chain's resources `chainRes c a` (`a` the
applier `Apply` was called on, `applyV3`'s value then), the request `rq` dispatched to the
method its first set field names (`dispatchKind`; the premise `dispatchOk`: not an empty request;
a compaction with its facts, `cmpAdmit`), with the apply thread's KV at `log` and the critical-section contract with
`v3` (`cPre v3`); the KV and `applyV3` (changed by an alarm request) after it (`dispatchStep`,
`chainAfter`), the result (`dispatchResult`). Its deferred metrics (`ApplySecObserve`, the
warnings) return. A write token of the store (`mvcc.storeWT E.γ`) is handed to the method
that may open a store write transaction (2026-10-13, unit 6). The certificates of the logs the
request may commit (`certPre`; 2026-10-14, unit T1). The apply thread's compaction resources
(`cmpOwn`), at `crev` before and at `dispatchCrev` after (M2's apply side, 2026-10-31: the compaction
arm, item 11). The rest state's premise `restReqOk` (the cluster-rows stage, 2026-11-02: a member
attributes request's member a member of `rs.mem`, `UpdateAttributes`' row). A grant (the
lease-grant stage, 2026-11-03; admitted where the cluster grants, `rqOk E.lg`) with its permits
(`grantPermRq`), the apply thread's half of the lessor's live set `T` (`ltHalf`) and the rest
buckets after it (`grantIds`, `grantRest`, the identity but for a grant dispatched with `v3`), its
answer (`grantRes`), and its outcome the lessor's verdict at `T` (`grantOutOk`; amendment (C),
2026-11-03). (The lease-expiry plan's E3 (c), 2026-11-05) The apply thread's half of the ids the
lessor ever had, `U` (`everOwn`), a grant's id new to them unless the lessor is monotone
(`grantFresh`), given back with an applied grant's id added (`grantIds`). (The lease-expiry plan's S2–S4, Q-S6 (A-ii), 2026-11-05) The
record's TTL `t` at least the grant's request (`grantTTLOk`). -/
abbrev apply.uberApplier.dispatch.spec : Prop :=
  ∀ (E : AEnv GF) (p : Loc) (opts : ApplierOptions) (c : apply.Chain) (a : GoInterface)
    (r : Loc) (rq : IRRModel) (skip v3 : Bool) (log F : mvcc.Log) (Pre Q Post : IProp GF)
    (rs : apply.RestM) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (crev : Int) (T : List w64)
    (U : List w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗ apply.uberIs E p opts ∗
      apply.irrWrapperIs r rq skip ∗ apply.chainRes c a info ∗
      structFieldRef uberApplier go!"applyV3" p ↦ a ∗ apply.applierSpec E c a ∗
      apply.kvOwn E log ∗ apply.certPreV v3 E c rq log ∗ mvcc.storeWT E.γ ∗ apply.cPre v3 E.P E.f Pre Q Post ∗
      ⌜apply.rqOk E.lm log rq ∧ apply.dispatchOk E.authOn rq ∧ apply.cmpAdmit E.γ.kb log rq⌝ ∗
      apply.cmpPermRq E rq ∗ apply.grantPermRq E rq ∗ apply.ltHalf E T ∗ apply.everOwn E U ∗ apply.grantFresh E rq U ∗
      apply.revokeOwn E rq ∗
      ⌜c.authOn = E.authOn⌝ ∗ mvcc.idxCert E.γ.idx F ∗
      E.FS ∗ (if v3 then apply.ciSplit E Pre else iprop(True)) ∗ ⌜apply.restReqOk rq rs⌝ ∗ E.RO rs ∗
      apply.cmpOwn E crev }}
    (App (App (Val (p @!! go.GoType.PointerType uberApplier.ty @!! go!"dispatch")) (Val #r)) (Val #v3))
  {{ (ar : Loc), RET #ar; apply.chainResAny c a ∗ E.FS ∗
      apply.cmpOwn E (apply.dispatchCrev c rq v3 crev) ∗
      ∃ (a' : GoInterface) (c' : apply.Chain) (o : apply.Outcome),
        structFieldRef uberApplier go!"applyV3" p ↦ a' ∗ apply.applierSpec E c' a' ∗
        apply.kvOwn E (o.logAfter log) ∗
        apply.ltHalf E (apply.revokeIds rq v3 o (apply.grantIds rq v3 o T)) ∗
        apply.everOwn E (apply.grantIds rq v3 o U) ∗ apply.revokeOwn E rq ∗
        (∃ t : w64, ⌜apply.grantTTLOk rq t⌝ ∗ E.RO (apply.revokeRest T rq v3 o
          (apply.grantRest t rq v3 o (apply.restAfter rq v3 rs)))) ∗
        ⌜apply.grantOutOk c rq v3 T o⌝ ∗ apply.cPost v3 Pre Post ∗
        ⌜apply.dispatchStep c rq v3 log o ∧ apply.chainAfter rq v3 c c' ∧
          apply.kvFloorOk rq v3 F log o ∧ a' = a ∧ c' = c⌝ ∗
        (∀ _ : v3 = true, apply.chainClass E.authMode info c rq o) ∗ apply.grantRes E rq o ar ∗
        apply.revokeAnsR E rq ar ∗ apply.resTrace ar ∗ apply.dispatchResult rq v3 log skip ar o }}

end spec

end EtcdGrove
end Perennial

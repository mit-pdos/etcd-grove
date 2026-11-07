/-
`apply.uberApplier.Apply` (uber_applier.go). Lean-first (no Rocq counterpart); the vocabulary is
`Proof/go_etcd_io/etcd/server/v3/etcdserver/apply/InvUber.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.InvUber
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.GrantRest

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

/-- **`a.Apply(r, shouldApplyV3)`**: the current applier's `Apply` with `dispatch`: the auth
layer's admin rejection (the state as it is), or `dispatch`'s outcome (`applyStep`, from the state
`x`). The wrapper's `SkipRangeExecution` is set only for a transaction (`apply.Apply` sets it so).
The backend's tokens lent (`kvOwnPre`, strict M1, 2026-11-05). The certificates
of the logs the request may commit (`certPre`; 2026-10-14, unit T1). A compaction admitted with
its facts (`cmpAdmit`), the apply thread's compaction resources at `x.crev` before and at `x'.crev`
after (`applyStep`'s clause; M2's apply side, 2026-10-31: items 4, 11). The rest state's premise
`restReqOk`, `dispatch`'s (the cluster-rows stage, 2026-11-02). A grant (the lease-grant stage,
2026-11-03) as `dispatch`'s: admitted at `rqOk E.lg`, with its permits, the half of the live set
`T` and the rest buckets after it (`grantIdsA`, `grantRestA`), its answer (`grantResA`; a revocation's, `revokeAnsRA`, the lease-expiry plan's X6), its
outcome the lessor's verdict at `T` (`grantOutOkA`; amendment (C), 2026-11-03), the ids the lessor
ever had `U` with an applied grant's id added (`everOwn`, `grantFresh`: the lease-expiry plan's E3
(c), 2026-11-05). (The lease-expiry plan's S2–S4, Q-S6 (A-ii), 2026-11-05) The
record's TTL `t` at least the grant's request (`grantTTLOk`). -/
abbrev apply.uberApplier.Apply.spec : Prop :=
  ∀ (E : AEnv GF) (p : Loc) (opts : ApplierOptions) (x : apply.ApplyKV) (r : Loc)
    (rq : IRRModel) (skip v3 : Bool) (F : mvcc.Log) (Pre Q Post : IProp GF) (rs : apply.RestM)
    (T U : List w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗ apply.uberIs E p opts ∗
      apply.irrWrapperIs r rq skip ∗ apply.uberOwn E p x.chain ∗ apply.kvOwnPre v3 E x.log Pre Q Post ∗
      apply.certPreV v3 E x.chain rq x.log ∗
      ⌜apply.rqOk E.lm x.log rq ∧ apply.dispatchOk E.authOn rq ∧ apply.cmpAdmit x.log rq⌝ ∗
      apply.cmpPermRq E rq ∗ apply.grantPermRq E rq ∗ apply.ltHalf E T ∗ apply.everOwn E U ∗ apply.grantFresh E rq U ∗
      apply.revokeOwn E rq ∗
      ⌜skip = true → rq.txn.isSome = true⌝ ∗ srvApi.kvLogLb E.γs F ∗ apply.applyTok E ∗
      E.FS ∗ (if v3 then apply.ciSplit E Pre else iprop(True)) ∗ ⌜apply.restReqOk rq rs⌝ ∗ E.RO rs ∗
      apply.cmpOwn E x.crev }}
    (App (App (Val (p @!! go.GoType.PointerType uberApplier.ty @!! go!"Apply")) (Val #r)) (Val #v3))
  {{ (ar : Loc), RET #ar; apply.applyTok E ∗ apply.bkRTOf E ∗ E.FS ∗ ∃ (x' : apply.ApplyKV) (out : apply.ApplyOut),
      apply.uberOwn E p x'.chain ∗ apply.kvOwn E x'.log ∗ apply.cPost v3 Pre Post ∗
      apply.ltHalf E (apply.revokeIdsA rq v3 out (apply.grantIdsA rq v3 out T)) ∗
      apply.everOwn E (apply.grantIdsA rq v3 out U) ∗ apply.revokeOwn E rq ∗
      (∃ t : w64, ⌜apply.grantTTLOk rq t⌝ ∗ E.RO (apply.revokeRestA T rq v3 out
        (apply.grantRestA t rq v3 out (apply.restOut rq v3 out rs)))) ∗
      ⌜apply.grantOutOkA x.chain rq v3 T out⌝ ∗ apply.cmpOwn E x'.crev ∗
      ⌜apply.applyStep rq v3 x x' out ∧ (out = .rejected ∨ ∃ o, out = .dispatched o skip) ∧
        apply.applyFloorOk rq v3 F x.log out⌝ ∗
      apply.resTrace ar ∗ apply.grantResA E rq out ar ∗ apply.revokeAnsRA E rq out ar ∗
      apply.applyResultIs rq v3 x.log ar out ∗
      apply.applyAuthRes E.authMode x.chain rq v3 out }}

end spec

end EtcdGrove
end Perennial

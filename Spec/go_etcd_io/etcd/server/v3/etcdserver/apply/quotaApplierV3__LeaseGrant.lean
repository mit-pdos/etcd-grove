/-
`apply.quotaApplierV3.LeaseGrant` (quota.go). Lean-first (no Rocq counterpart); the vocabulary is
`Proof/go_etcd_io/etcd/server/v3/etcdserver/apply/Chain.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.Chain

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

/-- **`a.LeaseGrant(lc)`**: the quota's `Available(lc)`, then the inner applier's `LeaseGrant`; `ErrNoSpace` in place of its `nil` if the quota said no.  (The lease-grant stage, 2.11, 2026-11-03: the chain's grant triple, `grantPre`/`grantPost`;
until then the generic triple of the methods that leave the log, over the write right `E.RW`.) -/
abbrev apply.quotaApplierV3.LeaseGrant.spec : Prop :=
  ∀ (E : AEnv GF) (c : apply.Chain) (inner : GoInterface) (p r : Loc) (rq : IRRModel) (g : LeaseGrantModel)
    (log : mvcc.Log) (T : List w64) (rs : apply.RestM) (U : List w64) (Pre Q Post : IProp GF)
    (info : go_etcd_io.etcd.server.v3.auth.AuthInfo),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗ apply.quotaIs p inner ∗ apply.applierSpec E c inner ∗
      apply.applyTok E ∗ apply.grantPre E (.quota c) (interface.mkOk (go.GoType.PointerType quotaApplierV3.ty) #p) info r rq g log T rs U
        Pre Q Post }}
    (App (Val (p @!! go.GoType.PointerType quotaApplierV3.ty @!! go!"LeaseGrant")) (Val #r))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); apply.applyTok E ∗ ∃ o : apply.Outcome,
      apply.grantPost E (.quota c) (interface.mkOk (go.GoType.PointerType quotaApplierV3.ty) #p) rq g log T rs U
        Pre Post resp err o }}

end spec

end EtcdGrove
end Perennial

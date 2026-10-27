/-
`apply.authApplierV3.DeleteRange` (auth.go). Lean-first (no Rocq counterpart); the vocabulary is
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

/-- **`aa.DeleteRange(r)`**: the auth store's `IsDeleteRangePermitted` and, with `PrevKv`, `IsRangePermitted` (an auth error: rejected), then the inner applier's `DeleteRange`. -/
abbrev apply.authApplierV3.DeleteRange.spec : Prop :=
  ∀ (E : AEnv GF) (c : apply.Chain) (inner : GoInterface) (p r : Loc) (rq : IRRModel) (o : OpFull) (log F : mvcc.Log)
    (Pre Q Post : IProp GF)
    (info : go_etcd_io.etcd.server.v3.auth.AuthInfo),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗ apply.authIs E p inner ∗ apply.applierSpec E c inner ∗
      apply.deletePre E (.auth E.authOn c) (interface.mkOk (go.GoType.PointerType authApplierV3.ty) #p) info r rq o log Pre Q Post ∗ mvcc.idxCert E.γ.idx F }}
    (App (Val (p @!! go.GoType.PointerType authApplierV3.ty @!! go!"DeleteRange")) (Val #r))
  {{ (resp trace : Loc) (err : GoInterface), RET (PairV (PairV #resp #trace) #err);
      apply.kvPostF E (.auth E.authOn c) (interface.mkOk (go.GoType.PointerType authApplierV3.ty) #p) info rq log F (apply.deleteAnswerIs log o resp err) Pre Post ∗
      apply.traceRes trace }}

end spec

end EtcdGrove
end Perennial

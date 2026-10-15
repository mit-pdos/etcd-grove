/-
`apply.authApplierV3.Apply` (auth.go). Lean-first (no Rocq counterpart); the vocabulary is
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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]

/-- **`aa.Apply(r, shouldApplyV3, applyFunc)`**: under `aa.mu` (whose resource is `aa.authInfo`), `authInfo` set from the request's header, if any; for a request that needs it (`needAdminPermission`), the auth store's `IsAdminPermitted`, whose error is the result (`&Result{Err: err}`, `applyFunc` not called); else the inner applier's `Apply`, whose `applyFunc` gets the chain's resources (`authInfo` among them); `authInfo` reset. -/
abbrev apply.authApplierV3.Apply.spec : Prop :=
  ∀ (E : AEnv GF) (c : apply.Chain) (inner : GoInterface) (p r : Loc) (rq : IRRModel)
    (skip v3 : Bool) (af : GoFunc) (A : IProp GF) (B : Loc → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗ apply.authIs E p inner ∗ apply.applierSpec E c inner ∗
      apply.irrWrapperIs r rq skip ∗ A ∗
      ({{ apply.chainRes (.auth c) (interface.mkOk (go.GoType.PointerType authApplierV3.ty) #p) ∗ A }} (App (App (Val #af) (Val #r)) (Val #v3))
        {{ (ar : Loc), RET #ar; apply.chainRes (.auth c) (interface.mkOk (go.GoType.PointerType authApplierV3.ty) #p) ∗ B ar }}) }}
    (App (App (App (Val (p @!! go.GoType.PointerType authApplierV3.ty @!! go!"Apply")) (Val #r)) (Val #v3)) (Val #af))
  {{ (ar : Loc), RET #ar;
      B ar ∨ (⌜apply.needAdminPermission rq = true⌝ ∗ A ∗ apply.rejectResultIs ar) }}

end spec

end EtcdGrove
end Perennial

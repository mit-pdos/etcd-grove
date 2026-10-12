/-
`apply.authApplierV3.RoleGet` (auth.go). Lean-first (no Rocq counterpart); the vocabulary is
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

/-- **`aa.RoleGet(r)`**: unless the user is an admin or has the role, an empty response with the auth store's error (the `authInfo` reset); else the inner applier's `RoleGet`. -/
abbrev apply.authApplierV3.RoleGet.spec : Prop :=
  ∀ (E : AEnv GF) (c : apply.Chain) (inner : GoInterface) (p r : Loc) (log : mvcc.Log) (Pre Q Post : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗ apply.authIs E p inner ∗ apply.applierSpec E c inner ∗
      (∃ n : GoString, apply.authRoleGetIs r n) ∗
      apply.mPre E (.auth c) (interface.mkOk (go.GoType.PointerType authApplierV3.ty) #p) log Pre Q Post }}
    (App (Val (p @!! go.GoType.PointerType authApplierV3.ty @!! go!"RoleGet")) (Val #r))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); apply.mPost E (.auth c) (interface.mkOk (go.GoType.PointerType authApplierV3.ty) #p) log Pre Post }}

end spec

end EtcdGrove
end Perennial

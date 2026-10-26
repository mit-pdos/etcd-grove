/-
`apply.authApplierV3.UserGet` (auth.go). Lean-first (no Rocq counterpart); the vocabulary is
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

/-- **`aa.UserGet(r)`**: unless the user is an admin or asks for itself, an empty response with the auth store's error (the `authInfo` reset); else the inner applier's `UserGet`. A3 (2026-10-23): a `nil` error says the principal passed as an admin or as the user itself (`userGetClass`). -/
abbrev apply.authApplierV3.UserGet.spec : Prop :=
  ∀ (E : AEnv GF) (c : apply.Chain) (inner : GoInterface) (p r : Loc) (log : mvcc.Log) (Pre Q Post : IProp GF)
    (info : go_etcd_io.etcd.server.v3.auth.AuthInfo),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗ apply.authIs E p inner ∗ apply.applierSpec E c inner ∗
      (((∃ n : GoString, apply.authUserGetIs r n) ∗ E.RW) ∗ ⌜apply.adminAdmitted E.authMode⌝) ∗
      apply.mPre E (.auth E.authOn c) (interface.mkOk (go.GoType.PointerType authApplierV3.ty) #p) info log Pre Q Post ∗ mvcc.storeWT E.γ ∗
      apply.ciSplit E Pre }}
    (App (Val (p @!! go.GoType.PointerType authApplierV3.ty @!! go!"UserGet")) (Val #r))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); apply.mPost E (.auth E.authOn c) (interface.mkOk (go.GoType.PointerType authApplierV3.ty) #p) log Pre Post ∗ applyErrIs err ∗
      (∀ _ : err = GoInterface.nil, ∃ n : GoString, apply.authUserGetIs r n ∗ apply.userGetClass E.authMode info n) }}

end spec

end EtcdGrove
end Perennial

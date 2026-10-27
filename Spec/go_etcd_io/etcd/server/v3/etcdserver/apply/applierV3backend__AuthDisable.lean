/-
`apply.applierV3backend.AuthDisable` (backend.go). Lean-first (no Rocq counterpart); the vocabulary is
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

/-- **`a.AuthDisable()`**: the auth store's `AuthDisable` (a critical section, or none); a fresh response with `newHeader()`. -/
abbrev apply.applierV3backend.AuthDisable.spec : Prop :=
  ∀ (E : AEnv GF) (p : Loc) (log : mvcc.Log) (Pre Q Post : IProp GF)
    (info : go_etcd_io.etcd.server.v3.auth.AuthInfo),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗ apply.backendIs E p ∗ ⌜apply.adminAdmitted E.authMode⌝ ∗
      apply.mPre E .backend (interface.mkOk (go.GoType.PointerType applierV3backend.ty) #p) info log Pre Q Post ∗ mvcc.storeWT E.γ ∗ E.RW }}
    (App (Val (p @!! go.GoType.PointerType applierV3backend.ty @!! go!"AuthDisable")) (Val #()))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); apply.mPost E .backend (interface.mkOk (go.GoType.PointerType applierV3backend.ty) #p) log Pre Post ∗ applyErrIs err }}

end spec

end EtcdGrove
end Perennial

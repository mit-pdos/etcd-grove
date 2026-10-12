/-
`apply.checkTxnPermission` (auth.go). Lean-first (no Rocq counterpart); the vocabulary is
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

/-- **`checkTxnPermission(as, ai, lessor, rt)`**: `IsRangePermitted` of every comparison's range, then `checkTxnReqsPermission` of both branches (nested transactions recursively): the first error, or `nil`; the `AuthInfo` kept, nothing written. -/
abbrev apply.checkTxnPermission.spec : Prop :=
  ∀ (st le : GoInterface) (γ : mvcc.StoreNames) (P : IProp GF) (f : val) (ai : Loc)
    (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (dq : DFrac) (rt : Loc) (t : TxnModel),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗ apply.isAuthStore st P f ∗ apply.isApplyLessor le γ P f ∗ ai ↦{dq} info ∗
      txn.txnRequestIs rt t }}
    (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.apply.checkTxnPermission))
      (Val #st)) (Val #ai)) (Val #le)) (Val #rt))
  {{ (err : GoInterface), RET #err; ai ↦{dq} info ∗ applyErrIs err }}

end spec

end EtcdGrove
end Perennial

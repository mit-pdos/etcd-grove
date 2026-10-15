/-
`apply.applierV3backend.LeaseRevoke` (backend.go). Lean-first (no Rocq counterpart); the vocabulary is
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

/-- **`a.LeaseRevoke(lc)`**: the lessor's `Revoke` (its deletions of the lease's keys committed through the store's writer, in one critical section), then a fresh response with `newHeader()`; the lessor's error. -/
abbrev apply.applierV3backend.LeaseRevoke.spec : Prop :=
  ∀ (E : AEnv GF) (p r : Loc) (rq : IRRModel) (id : w64) (log : mvcc.Log)
    (Pre Q Post : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗ apply.backendIs E p ∗
      apply.revokePre E .backend (interface.mkOk (go.GoType.PointerType applierV3backend.ty) #p) r rq id log Pre Q Post }}
    (App (Val (p @!! go.GoType.PointerType applierV3backend.ty @!! go!"LeaseRevoke")) (Val #r))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
      apply.kvPost E .backend (interface.mkOk (go.GoType.PointerType applierV3backend.ty) #p) rq log (apply.revokeOutcomeIs resp err) Pre Post }}

end spec

end EtcdGrove
end Perennial

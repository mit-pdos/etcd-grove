/-
`apply.applierV3backend.LeaseGrant` (backend.go). Lean-first (no Rocq counterpart); the vocabulary is
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

/-- **`a.LeaseGrant(lc)`**: the lessor's `Grant` (a critical section, or none), a fresh response with the lease's `ID`, `TTL()` and `newHeader()` if it succeeded. -/
abbrev apply.applierV3backend.LeaseGrant.spec : Prop :=
  ∀ (E : AEnv GF) (p r : Loc) (log : mvcc.Log) (Pre Q Post : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗ apply.backendIs E p ∗
      (∃ g : LeaseGrantModel, apply.leaseGrantIs r g) ∗
      apply.mPre E .backend (interface.mkOk (go.GoType.PointerType applierV3backend.ty) #p) log Pre Q Post }}
    (App (Val (p @!! go.GoType.PointerType applierV3backend.ty @!! go!"LeaseGrant")) (Val #r))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); apply.mPost E .backend (interface.mkOk (go.GoType.PointerType applierV3backend.ty) #p) log Pre Post }}

end spec

end EtcdGrove
end Perennial

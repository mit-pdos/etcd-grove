/-
`apply.applierV3Corrupt.LeaseGrant` (corrupt.go). Lean-first (no Rocq counterpart); the vocabulary is
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

/-- **`a.LeaseGrant(lc)`**: `ErrCorrupt`; nothing written. -/
abbrev apply.applierV3Corrupt.LeaseGrant.spec : Prop :=
  ∀ (E : AEnv GF) (c : apply.Chain) (inner : GoInterface) (p r : Loc) (log : mvcc.Log) (Pre Q Post : IProp GF)
    (info : go_etcd_io.etcd.server.v3.auth.AuthInfo),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗ apply.corruptIs p inner ∗
      ((∃ g : LeaseGrantModel, apply.leaseGrantIs r g ∗ lease.leaseGranted E.γ.leases g.id) ∗ E.RW) ∗
      apply.mPre E (.corrupt c) (interface.mkOk (go.GoType.PointerType applierV3Corrupt.ty) #p) info log Pre Q Post ∗ mvcc.storeWT E.γ }}
    (App (Val (p @!! go.GoType.PointerType applierV3Corrupt.ty @!! go!"LeaseGrant")) (Val #r))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); apply.mPost E (.corrupt c) (interface.mkOk (go.GoType.PointerType applierV3Corrupt.ty) #p) log Pre Post ∗ applyErrIs err }}

end spec

end EtcdGrove
end Perennial

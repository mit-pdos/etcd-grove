/-
`apply.applierV3backend.DowngradeInfoSet` (backend.go). Lean-first (no Rocq counterpart); the vocabulary is
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

/-- **`a.DowngradeInfoSet(r, shouldApplyV3)`**: the cluster's `SetDowngradeInfo` (a critical section, or none). -/
abbrev apply.applierV3backend.DowngradeInfoSet.spec : Prop :=
  ∀ (E : AEnv GF) (p r : Loc) (v3 : Bool) (log : mvcc.Log) (Pre Q Post : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗ apply.backendIs E p ∗
      (∃ dm : DowngradeModel, apply.downgradeInfoSetIs r dm) ∗
      apply.mPreV v3 E .backend (interface.mkOk (go.GoType.PointerType applierV3backend.ty) #p) log Pre Q Post }}
    (App (App (Val (p @!! go.GoType.PointerType applierV3backend.ty @!! go!"DowngradeInfoSet")) (Val #r)) (Val #v3))
  {{ RET #(); apply.mPostV v3 E .backend (interface.mkOk (go.GoType.PointerType applierV3backend.ty) #p) log Pre Post }}

end spec

end EtcdGrove
end Perennial

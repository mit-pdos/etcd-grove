/-
`apply.newApplierV3Corrupt` (corrupt.go). Lean-first (no Rocq counterpart); the vocabulary is
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

/-- **`newApplierV3Corrupt(a)`**: the corrupt applier over `a` (an applier of the chain `c`): a pointer whose interface value is an applier of the chain `corrupt c`. -/
abbrev apply.newApplierV3Corrupt.spec : Prop :=
  ∀ (E : AEnv GF) (c : apply.Chain) (a : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗ apply.applierSpec E c a }}
    (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.apply.newApplierV3Corrupt)) (Val #a))
  {{ (p : Loc), RET #p;
      apply.applierSpec E (.corrupt c) (interface.mkOk (go.GoType.PointerType applierV3Corrupt.ty) #p) }}

end spec

end EtcdGrove
end Perennial

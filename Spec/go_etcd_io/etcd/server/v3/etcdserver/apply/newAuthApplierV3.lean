/-
`apply.newAuthApplierV3` (auth.go). Lean-first (no Rocq counterpart); the vocabulary is
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

/-- **`newAuthApplierV3(as, base, lessor)`**: the auth applier over `base` (an applier of the chain `c`), the auth store `as` and the lessor `lessor` with their contracts: a pointer whose interface value is an applier of the chain `auth c` (its mutex made, with its `authInfo`). -/
abbrev apply.newAuthApplierV3.spec : Prop :=
  ∀ (E : AEnv GF) (c : apply.Chain) (st base le : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗ apply.isAuthStore st E.P E.f ∗ apply.isApplyLessor le E.γ E.P E.f ∗
      apply.applierSpec E c base }}
    (App (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.apply.newAuthApplierV3))
      (Val #st)) (Val #base)) (Val #le))
  {{ (p : Loc), RET #p;
      apply.applierSpec E (.auth c) (interface.mkOk (go.GoType.PointerType authApplierV3.ty) #p) }}

end spec

end EtcdGrove
end Perennial

/-
`apply.newApplierV3Backend` (backend.go). Lean-first (no Rocq counterpart); the vocabulary is
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

/-- **`newApplierV3Backend(opts)`**: the backend applier over the options `opts` (a logger, the KV `E.s`, the components with their contracts): an applier value of the chain `backend`. -/
abbrev apply.newApplierV3Backend.spec : Prop :=
  ∀ (opts : ApplierOptions),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply }}
    (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.apply.newApplierV3Backend)) (Val #opts))
  {{ (a : GoInterface), RET #a;
      -- (the auth plan's E2m) its shape: a backend applier with its options, read-only
      (∃ p : Loc, ⌜a = interface.mkOk (go.GoType.PointerType applierV3backend.ty) #p⌝ ∗
        structFieldRef applierV3backend go!"options" p ↦□ opts) ∗
      □ (∀ E : AEnv GF, apply.backendOptsOk E opts -∗ apply.applierSpec E .backend a) }}

end spec

end EtcdGrove
end Perennial

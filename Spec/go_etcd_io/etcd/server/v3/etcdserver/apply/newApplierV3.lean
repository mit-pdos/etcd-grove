/-
`apply.newApplierV3` (uber_applier.go). Lean-first (no Rocq counterpart); the vocabulary is
`Proof/go_etcd_io/etcd/server/v3/etcdserver/apply/InvUber.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.InvUber

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

/-- **`newApplierV3(opts)`**: the base chain (`authApplierV3` over `quotaApplierV3` over
`applierV3backend`) over the options `opts`, whose contracts hold in `E`. -/
abbrev apply.newApplierV3.spec : Prop :=
  ∀ (E : AEnv GF) (opts : ApplierOptions),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗ apply.backendOptsOk E opts }}
    (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.apply.newApplierV3)) (Val #opts))
  {{ (a : GoInterface), RET #a; apply.applierSpec E apply.baseChain a }}

end spec

end EtcdGrove
end Perennial

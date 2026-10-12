/-
`apply.NewUberApplier` (uber_applier.go). Lean-first (no Rocq counterpart); the vocabulary is
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

/-- **`NewUberApplier(opts)`**: an `*uberApplier` `p` over the options `opts` (whose contracts
hold in `E`): its fields from the options and the base chain (`uberIs`, persistent), its current
applier the chain the alarm store's answers ask for (`restoreAlarms`: `alarmChain ns cr`). -/
abbrev apply.NewUberApplier.spec : Prop :=
  ∀ (E : AEnv GF) (opts : ApplierOptions),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗ apply.backendOptsOk E opts }}
    (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.apply.NewUberApplier)) (Val #opts))
  {{ (ua : GoInterface), RET #ua; ∃ p : Loc,
      ⌜ua = interface.mkOk (go.GoType.PointerType uberApplier.ty) #p⌝ ∗ apply.uberIs E p opts ∗
      ∃ ns cr : Bool, apply.uberOwn E p (apply.alarmChain ns cr) }}

end spec

end EtcdGrove
end Perennial

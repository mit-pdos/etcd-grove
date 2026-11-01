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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]

/-- **`newApplierV3(opts)`**: the base chain (`authApplierV3` over `quotaApplierV3` over
`applierV3backend`) over the options `opts`, whose contracts hold in `E` (2026-11-01, J8a: no reader
resource `E.RD`, which the auth layer's `Apply` borrows from its caller; until then its mutex took one). -/
abbrev apply.newApplierV3.spec : Prop :=
  ∀ (opts : ApplierOptions),
  -- the backend stays under its quota (audit phase B3, D19h)
  apply.backendUnderQuota →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply }}
    (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.apply.newApplierV3)) (Val #opts))
  {{ (a : GoInterface), RET #a;
      -- (the auth plan's E2m) its shape: auth over quota over the backend with `opts`
      apply.baseShape opts a ∗
      □ (∀ E : AEnv GF, apply.backendOptsOk E opts -∗
        apply.applierSpec E (apply.baseChain E.authOn) a) ∗
      -- (the auth plan's E3k) its auth layer (`baseAuth`)
      □ (∀ E : AEnv GF, apply.backendOptsOk E opts -∗ apply.baseAuth E opts a) }}

end spec

end EtcdGrove
end Perennial

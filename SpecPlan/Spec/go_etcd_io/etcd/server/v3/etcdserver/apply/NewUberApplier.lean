/-
`apply.NewUberApplier(opts)` (`uber_applier.go:226-238`): the base chain (`newApplierV3`: auth over
quota over backend, over the options), the uber-applier over it, its current chain chosen by the
alarm store (`restoreAlarms`).

**Users.** `EtcdServer.NewServer` (`server.go:357`, 2e: the stores at the backend's state after
bootstrap), `EtcdServer.applySnapshot` (`server.go:1181`, 2d: the stores rebuilt over the
snapshot's image). Snippet `examples/specreq/apply/apply.go` (`ReqNewUber`).

**Proof sketch.** `newApplierV3(opts)` (`newApplierV3.spec`: `beAt b mc γ γc R` from `optsOk`, the
base chain `applierAt v baseLayers b aa`, `stAt b σ` from `optsSt`); the struct allocated
(`uberAt p b aa …`); `restoreAlarms` (`uberApplier.restoreAlarms.spec`: the chain the alarms select);
`smAt_unfold` packs `uberChain p (chainLayers σ) ∗ stAt b σ`; `isUber` is the fields with the
concrete method's spec (`uberApplier.Apply.spec`) as its bundle (`isUber_apply`).

**Changes** from `specs-ref`'s `NewUberApplier.lean`: no `backendUnderQuota` premise (the quota's
refusal is a margin of the result, `resMatch`); one spec for every mode (the auth mode, the alarms,
leases, compaction are in `σ`); the options as two slots (`optsOk`, `optsSt`) over the callees'
vocabulary, not the old `AEnv`.
verify-round (A9 F2, F3, F6): `optsOk` now carries the backends' post-lock hook contracts under `R`
(`hooksOk`), `optsSt`'s `lessorSt` every key's lease live, the lessor's backend the options' and
its range deleter `o.KV'`'s (`kvDelOk`): what the backend's `Put`, `Txn`, `LeaseGrant`,
`LeaseCheckpoint`, `LeaseRevoke` and admin methods take. The callers (2e's `NewServer`, 2d's
`applySnapshot`) establish them: the lessor's hook by 4a's `leaseBeHook_intro`/`leaseHookRun_intro`,
the auth store's and `kvDelOk` by the introductions requested in `repair-apply-txn.md`.

**Margin.** None. (Round 1: `uberOpts ua opts`, persistent, gets the stores back out of `smAt`: `smAt_optsSt`, `smAt_alarms`.)
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.ApiResult

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Apply

open Iris Iris.BI EtcdModel

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]

/-- **An uber-applier over the options**, its state machine at the stores' state `σ`. -/
def NewUberApplier.spec : Prop :=
  ∀ (opts : go_etcd_io.etcd.server.v3.etcdserver.apply.ApplierOptions) (mc : MemberCfg)
    (γ : Cluster) (γc : Membership.CNames) (R : IProp GF) (σ : State),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗
      optsOk opts mc γ γc R ∗ optsSt opts σ }}
    (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.apply.NewUberApplier)) (Val #opts))
  {{ (ua : GoInterface), RET #ua; isUber ua mc γ γc R ∗ uberOpts ua opts ∗ smAt ua σ }}

end spec

end Apply
end EtcdGrove
end Perennial

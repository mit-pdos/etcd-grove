/-
`(*DaemonSetsController).processNextWorkItem(ctx)` (`daemon_controller.go:401`): one key off the
work queue. Lean-first; Stage 3 of the autoverify run (`notes/k8s-daemonset-run/design.md`, "S1's
invariant", "The controller object").

**What the code does** (read 2026-11-03 at the pin): `Get()` a key (`false` if the queue is shutting
down); defer `Done(key)`; run the sync handler (`syncDaemonSet`) on it; on `nil`, `Forget(key)`;
otherwise `HandleError` and `AddRateLimited(key)`; return `true`.

**What a worker holds**: the controller (`isDsc`), the two invariants (`apiInv`, `s1Inv`: the sync's
writes go through them), its thread token (it borrows each read's slot from the controller's
pools). Between `Get` and `Done` it holds the queue's token of the key, which it trades inside
`s1Inv` for the sync token of the key's owner (`syncTok`; the key is canonical,
the queue's item predicate `keyCanon`) and trades back after the sync.
-/
module

public import Proof.k8s_io.kubernetes.pkg.controller.daemon.SyncDefs

@[expose] public section

set_option autoImplicit false

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace dsctl

open Iris Iris.BI apimodel k8s_io.kubernetes.pkg.controller.daemon

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.kubernetes.pkg.controller.daemon.Assumptions]

/-- **`dsc.processNextWorkItem(ctx)`**: one key processed; `false` only once the queue is shutting
down. -/
abbrev DaemonSetsController.processNextWorkItem.spec : Prop :=
  ∀ (dsc : Loc) (c : DscComp)
    (cfg : github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Config)
    (γa : ApiNames) (F : DscFams GF) (γ : S1Names) (ctx : GoInterface),
  {{ dscEnv dsc c cfg γa F γ ∗ threadTok ∗ ⌜ctx ≠ interface.nil⌝ }}
    (App (Val (dsc @!! go.GoType.PointerType DaemonSetsController.ty @!! go!"processNextWorkItem"))
      (Val #ctx))
  {{ (b : Bool), RET #b; threadTok ∗ (⌜b = true⌝ ∨ workqueue.shutdownLb c.γq.tq) }}

end spec

end dsctl
end EtcdGrove
end Perennial

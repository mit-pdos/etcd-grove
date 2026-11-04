/-
`(*DaemonSetsController).syncDaemonSet(ctx, key)` (`daemon_controller.go:1281`): the sync of one
DaemonSet. Lean-first; Stage 3 of the autoverify run (`notes/k8s-daemonset-run/design.md`). Gap
D2: its body is the named hypothesis `DaemonSetsController__syncDaemonSet_body.lean`.

**What the code does** (read 2026-11-03 at the pin): split the key (an error ends the sync); the
consistency store's `EnsureReady(owner)` (an error, the owner's writes not yet seen, ends it); the
DaemonSet from the lister (not found: `DeleteExpectations`, `Clear`, `nil`); the nodes from the
lister; an empty selector ends it (an event); `KeyFunc(ds)`; a DaemonSet being deleted ends it;
`constructHistory` (the current revision's hash); if the expectations are not satisfied, only
`updateDaemonSetStatus`; otherwise `updateDaemonSet` (manage, rolling update, history cleanup) and
`updateDaemonSetStatus`.

**The spec**: for any key, with the sync token of the owner the key names (`ownerOf key`; none for a
key `SplitMetaNamespaceKey` rejects), the sync keeps the invariants (its writes, through
`apiInv` and `s1Inv`, keep `s1Ok`: S1 for every DaemonSet) and gives the token back. Its result
is any error the worker can format (`fmt.argOk`: it logs it with `fmt.Errorf`).
-/
module

public import Proof.k8s_io.kubernetes.pkg.controller.daemon.S1Inv
public import Spec.fmt.Errorf

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

/-- **The sync's token for `key`**: the sync token of the owner the key names, if any. -/
def keySyncTok (γ : S1Names) (c : DscComp)
    (key : GoString) : IProp GF :=
  match ownerOf key with
  | some o => syncTok γ c o
  | none => iprop(True)

/-- **`dsc.syncDaemonSet(ctx, key)`**: see the file header. -/
abbrev DaemonSetsController.syncDaemonSet.spec : Prop :=
  ∀ (dsc : Loc) (c : DscComp)
    (cfg : github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Config)
    (γa : ApiNames) (F : DscFams GF) (γ : S1Names) (ctx : GoInterface) (key : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.kubernetes.pkg.controller.daemon ∗
      isDsc dsc c cfg γa F ∗ apiInv γa γ ∗ s1Inv γ c ∗ threadTok ∗ ⌜ctx ≠ interface.nil⌝ ∗
      keySyncTok γ c key }}
    (App (App (Val (dsc @!! go.GoType.PointerType DaemonSetsController.ty @!! go!"syncDaemonSet"))
      (Val #ctx)) (Val #key))
  {{ (err : GoInterface), RET #err; threadTok ∗ keySyncTok γ c key ∗ fmt.argOk err }}

end spec

end dsctl
end EtcdGrove
end Perennial

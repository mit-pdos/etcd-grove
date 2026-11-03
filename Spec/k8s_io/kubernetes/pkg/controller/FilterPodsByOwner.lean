/-
`controller.FilterPodsByOwner(podIndexer, owner, ownerKind, includeOrphanedPods)`
(`controller_utils.go:1176`): the indexer's pods under the owner's controller key
(`PodControllerIndexKey(ns, {Name, Kind, UID})`, `ByIndex(PodControllerIndex, ...)`) and, if asked,
under the namespace's orphan key; an error for an owner with no namespace, name or UID. Lean-first;
Stage 3, track B.

Stated over the pod informer (`infAt`, the controller index `podCtlIndexed`): every pod of the
informer's view, at a version at least a bound `L` the caller knows, whose controller key is the
owner's is in the result, and every pod of the result is a logged one. (Each `ByIndex` is a
linearization point of its own; the first, the owner's key, gives the view.)
-/
module

public import Proof.k8s_io.kubernetes.pkg.controller.daemon.SyncDefs

@[expose] public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace dsctl

open Iris Iris.BI apimodel consistency cache k8s_io.kubernetes.pkg.controller

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.kubernetes.pkg.controller.Assumptions]

/-- **`FilterPodsByOwner(idx, &ds.ObjectMeta, kind, b)`**: see the file header. -/
abbrev FilterPodsByOwner.spec : Prop :=
  ∀ (γa : ApiNames) (I : InfLoc) (Fam : Nat → Fn GF) (ds : Loc) (d : kd.apps.DaemonSet)
    (kind : GoString) (b : Bool) (L : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.kubernetes.pkg.controller ∗ infAt γa .pods I Fam ∗ podCtlIndexed I Fam ∗
      tsReader I.ts I.γt (informer.infObj I.γi .pods) Fam ∗ informer.infRvLb I.γi L ∗
      □ dsAt ds DFrac.discard d }}
    (App (App (App (App (Val (@! k8s_io.kubernetes.pkg.controller.FilterPodsByOwner))
      (Val #(interface.mkOk (go.GoType.PointerType k8s_io.client_go.tools.cache.cache.ty) #I.ca :
        k8s_io.client_go.tools.cache.Indexer)))
      (Val #(ds.[k8s_io.api.apps.v1.DaemonSet, go!"ObjectMeta"]))) (Val #kind)) (Val #b))
  {{ (pl : GoSlice) (err : GoInterface), RET (PairV #pl #err);
      tsReader I.ts I.γt (informer.infObj I.γi .pods) Fam ∗ fmt.argOk err ∗
      (⌜err ≠ interface.nil⌝ ∨ ⌜err = interface.nil⌝ ∗ ∃ ps, podsAt pl (DFrac.own 1) ps ∗
        ∃ (σp : apimodel.St) (v : Nat), pastSt γa σp ∗ ⌜L ≤ v ∧
          (∀ k p, informer.tableAt σp.pods.log v !! k = some (.pod p) →
            podCtlKey p.ObjectMeta'.Namespace' (ctlOf p) = podCtlKey d.ObjectMeta'.Namespace'
              (some ⟨go!"", kind, d.ObjectMeta'.Name', d.ObjectMeta'.UID', none, none⟩) → p ∈ ps) ∧
          (∀ p ∈ ps, ∃ ch ∈ σp.pods.log, ch.obj = .pod p)⌝) }}

end spec

end dsctl
end EtcdGrove
end Perennial

/-
`NewTypedDaemonSetInformerWithOptions(client, namespace, options)` (gap D2: names only; its body a
named hypothesis to come, as `RealPodControl__createPods_body.lean`): a shared index informer
(`cache.NewSharedIndexInformerWithOptions`) over the list-watch of `.daemonSets` built from the
client's `AppsV1().DaemonSets(namespace)` `List`/`Watch` (wrapped by
`ToListWatcherWithWatchListSemantics`), example object `&DaemonSet{}`, in a typed wrapper. With
all namespaces, resync `0`, no name and no tweak (the factory's), the list-watch closures meet
`lwOk` (`RefInf.lean`) from the clientset and the read access `apiReader` (each `List`/`Watch`
is logically atomic over `apiState`, fired through `apiReader_read`); the indexers `nfv` are
the store's, with relations `Fam (nids n)`. Lean-first; the DaemonSet run's track A. The informer's not-started token is the caller's (`γns`, whose start-lock half it
takes; decision R6).
-/
module

public import Proof.k8s_io.client_go.informers.Defs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace appsinformers

open Iris Iris.BI apimodel cache informer informers

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.informers.apps.v1.Assumptions]
variable [cache_sem : k8s_io.client_go.tools.cache.Assumptions]
variable [ctx_sem : _root_.Perennial.context.Assumptions]

/-- **`NewTypedDaemonSetInformerWithOptions(client, "", options)`**: see the file header. -/
abbrev NewTypedDaemonSetInformerWithOptions.spec : Prop :=
  ∀ (c : Loc) (γa : ApiNames) (cfg : github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Config) (Fam : Nat → Fn GF)
    (o : k8s_io.client_go.informers.internalinterfaces.InformerOptions) (dn : DFrac)
    (nfv : GMap GoString GoFunc) (nids : GMap GoString Nat) (γns : GName),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.informers.apps.v1 ∗ clientsetAt c γa cfg false ∗ apiReader γa ∗ keysOk γa ∗
      ⌜o.ResyncPeriod' = W64 0 ∧ o.InformerName' = null ∧ o.TweakListOptions' = func.nil ∧
        GMap.size nfv ≤ 2 ^ 62⌝ ∗
      o.Indexers' ↦${dn} nfv ∗ □ (∀ γi : InfNames, fnsOk (infObj γi .daemonSets) nfv (GMap.fmap Fam nids)) ∗
      nsLock γns false }}
    (App (App (App (Val (@! k8s_io.client_go.informers.apps.v1.NewTypedDaemonSetInformerWithOptions)) (Val #(clientVal c)))
      (Val #(go!"" : GoString))) (Val #o))
  {{ (x : GoInterface), RET #x; ∃ I : InfH, ⌜I.γi.ns = γns⌝ ∗ isInformer x γa .daemonSets I Fam ∗ infRunOk x I.γi ∗
      [∗map] n ↦ j ∈ nids, infIdx I n j }}

end spec

end appsinformers
end EtcdGrove
end Perennial

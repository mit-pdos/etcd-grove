/-
`cache.NewSharedIndexInformerWithOptions(lw, exampleObject, options)` (`shared_informer.go`):
a `*sharedIndexInformer` over the list-watch `lw` (meeting `lwOk` for resource `r`), with a store
keyed by `DeletionHandlingMetaNamespaceKeyFunc` and indexed by `options.Indexers` (relations
`Fam (nids n)`), resync `0`, no metrics provider or shard selector. The informer invariant is
allocated here (the store empty, nothing listed; the FIFO's state names preallocated), so the
informer's view holds from its construction: `isInformer` of it, runnable (`infRunOk`), each
index registered. Its not-started token is the caller's (`γns`, whose start-lock half `nsLock γns
false` it takes: the factory preallocates it, decision R6). Lean-first; the DaemonSet run's track A.
-/
module

public import Proof.k8s_io.client_go.tools.cache.SIIAt

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cache

open Iris Iris.BI apimodel cache informer k8s_io.client_go.tools.cache

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.tools.cache.Assumptions]
variable [ctx_sem : _root_.Perennial.context.Assumptions]

/-- **`NewSharedIndexInformerWithOptions(lw, obj, options)`**: see the file header. -/
abbrev NewSharedIndexInformerWithOptions.spec : Prop :=
  ∀ (lw : GoInterfaceOk) (γa : ApiNames) (cfg : github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Config) (r : Res) (p : Loc) (Fam : Nat → Fn GF)
    (o : SharedIndexInformerOptions) (dn : DFrac) (nfv : GMap GoString GoFunc)
    (nids : GMap GoString Nat) (γns : GName),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.tools.cache ∗ lwOk lw γa cfg r ∗ keysOk γa ∗
      ⌜o.ResyncPeriod' = W64 0 ∧ o.InformerMetricsProvider' = interface.nil ∧
        o.ShardSelector' = interface.nil ∧ GMap.size nfv ≤ 2 ^ 62⌝ ∗
      o.Indexers' ↦${dn} nfv ∗ □ (∀ γi : InfNames, fnsOk (infObj γi r) nfv (GMap.fmap Fam nids)) ∗
      nsLock γns false }}
    (App (App (App (Val (@! NewSharedIndexInformerWithOptions)) (Val #(GoInterface.ok lw)))
      (Val #(interface.mkOk (go.GoType.PointerType (resObjTy r)) #p :
        k8s_io.apimachinery.pkg.runtime.Object))) (Val #o))
  {{ (s : Loc), RET #(interface.mkOk (go.GoType.PointerType sharedIndexInformer.ty) #s : SharedIndexInformer);
      ∃ I : InfH, ⌜I.γi.ns = γns⌝ ∗
        isInformer (interface.mkOk (go.GoType.PointerType sharedIndexInformer.ty) #s) γa r I Fam ∗
        infRunOk (interface.mkOk (go.GoType.PointerType sharedIndexInformer.ty) #s) I.γi ∗
        [∗map] n ↦ j ∈ nids, infIdx I n j }}

end spec

end cache
end EtcdGrove
end Perennial

/-
`(*daemonSetLister).GetPodDaemonSets(pod)` (`listers/apps/v1/daemonset_expansion.go:43`): the
DaemonSets of the pod's namespace whose (non-empty) selector selects its labels; an error if it has
no labels or none is found. Lean-first; phase 4 of `notes/k8s-daemonset-plan.md` (the label
selector boundary).
-/
module

public import Proof.k8s_io.client_go.listers.apps.v1.ExpansionDefs
public import Spec.k8s_io.client_go.listers.apps.v1.daemonSetNamespaceLister__List

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace appslisters

open Iris Iris.BI cache listers labels k8s_io.client_go.listers.apps.v1

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.listers.apps.v1.Assumptions]
variable [package_sem' : k8s_io.client_go.listers.Assumptions]

open Classical in
/-- What `GetPodDaemonSets` returns for a pod of namespace `pns` and labels `L`, at the
linearization point's state `σ`: an error if `L` is empty; otherwise, of the DaemonSets `ls`
the namespace lister lists (`nsKeys`), those it picks (`selPicks`: same namespace, a non-empty selector
selecting `L`), in order: an error if none, else a slice of them. -/
def podDSPost (OK : GoInterface → IProp GF) (F : Fn GF) (σ : St) (pns : GoString)
    (L : GMap GoString GoString) (sl : GoSlice) (err : GoInterface) : IProp GF :=
  iprop((⌜GMap.size L = 0 ∧ err ≠ interface.nil⌝) ∨
    (∃ (q : Loc) (ks : List GoString) (ls : List Loc) (bs : List Bool),
      ⌜GMap.size L ≠ 0⌝ ∗ nsKeys F σ pns q ks ∗
      ⌜ls.map (ptrObj k8s_io.api.apps.v1.DaemonSet.ty) = ks.map (objAt σ.items) ∧
        bs.length = ls.length⌝ ∗
      □ ([∗list] i ↦ d ∈ ls, ∃ (dns : GoString) (S : Option SelV), dsView d dns S ∗
        ⌜bs[i]? = some (decide (selPicks (some pns) L S dns))⌝) ∗
      □ ([∗list] d ∈ ls, OK (ptrObj k8s_io.api.apps.v1.DaemonSet.ty d)) ∗
      (if flagged ls bs = [] then iprop(⌜err ≠ interface.nil⌝)
       else iprop(⌜err = interface.nil⌝ ∗ sl ↦* flagged ls bs))))

/-- **`s.GetPodDaemonSets(pod)`**, logically atomic (it reads the store once, through the namespace
lister's `List`), for the DaemonSet lister `s` over the cache `ca` (its stored DaemonSets
readable, `dsSel`) and a pod whose metadata is readable (`metaView`: namespace `pns`, labels `L`):
`podDSPost`. -/
abbrev daemonSetLister.GetPodDaemonSets.spec : Prop :=
  ∀ (s : Loc) (dq : DFrac) (ca ts : Loc) (γ : TsNames) (OK : GoInterface → IProp GF)
    (Fam : Nat → Fn GF) (kf : GoFunc) (res : k8s_io.apimachinery.pkg.runtime.schema.GroupResource)
    (ns0 : GoString) (pod : Loc) (pns pname : GoString) (L : GMap GoString GoString) (F : Fn GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.listers.apps.v1 ∗
      s.[daemonSetLister, go!"ResourceIndexer"] ↦{dq} riVal ca res ns0 ∗
      isCache ca ts γ OK Fam kf ∗ tsReader ts γ OK Fam ∗
      typedOK OK k8s_io.api.apps.v1.DaemonSet.ty ∗ qOk OK pns ∗ dsSel OK ∗
      metaView (GF := GF) (structFieldRef k8s_io.api.core.v1.Pod go!"ObjectMeta" pod) pns pname L }}
  <<{ ∀∀ σ, storeSt γ σ ∗
      ⌜noNil σ.items ∧ (pns ≠ [] → St.fns Fam σ !! go!"namespace" = some F)⌝ }>>
    (App (Val (s @!! go.GoType.PointerType daemonSetLister.ty @!! go!"GetPodDaemonSets"))
      (Val #pod))
    @@ ∅
  <<{ storeSt γ σ ∗ ⌜noNil σ.items ∧ (pns ≠ [] → St.fns Fam σ !! go!"namespace" = some F)⌝ }>>
  {{ (sl : GoSlice) (err : GoInterface), RET (PairV #sl #err);
      podDSPost OK F σ pns L sl err ∗ s.[daemonSetLister, go!"ResourceIndexer"] ↦{dq} riVal ca res ns0 ∗
      tsReader ts γ OK Fam }}

end spec

end appslisters
end EtcdGrove
end Perennial

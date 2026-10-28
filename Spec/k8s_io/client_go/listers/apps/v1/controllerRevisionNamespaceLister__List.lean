/-
`controllerRevisionNamespaceLister.List` (`listers/apps/v1/controllerrevision.go`, promoted from the embedded
`listers.ResourceIndexer[*v1.ControllerRevision]`): the generic lister's `List`. Lean-first.
-/
module

public import Spec.k8s_io.client_go.listers.ResourceIndexer__List
public import GeneratedProof.k8s_io.client_go.listers.apps.v1
public import Spec.k8s_io.client_go.listers.apps.v1.controllerRevisionNamespaceLister__Get

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace appslisters

open Iris Iris.BI cache listers k8s_io.client_go.listers.apps.v1

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.listers.apps.v1.Assumptions]
variable [package_sem' : k8s_io.client_go.listers.Assumptions]

/-- **`l.List`** for the ControllerRevision namespace lister `l` over the cache `ca`: `ResourceIndexer.List`'s spec at `X = v1.ControllerRevision`. -/
abbrev controllerRevisionNamespaceLister.List.spec : Prop :=
  ∀ (ca ts : Loc) (γ : TsNames) (OK : GoInterface → IProp GF) (Fam : Nat → Fn GF)
    (kf : GoFunc) (res : k8s_io.apimachinery.pkg.runtime.schema.GroupResource) (ns : GoString)
    (sel : GoInterface) (F : Fn GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.listers.apps.v1 ∗ isCache ca ts γ OK Fam kf ∗
      tsReader ts γ OK Fam ∗ typedOK OK k8s_io.api.apps.v1.ControllerRevision.ty ∗ everySel sel ∗ qOk OK ns }}
  <<{ ∀∀ σ, storeSt γ σ ∗
      ⌜noNil σ.items ∧ (ns ≠ [] → St.fns Fam σ !! go!"namespace" = some F)⌝ }>>
    (App (Val #(methods controllerRevisionNamespaceLister.ty go!"List" #(crnlVal ca res ns))) (Val #sel))
    @@ ∅
  <<{ storeSt γ σ ∗ ⌜noNil σ.items ∧ (ns ≠ [] → St.fns Fam σ !! go!"namespace" = some F)⌝ }>>
  {{ (sl : GoSlice) (err : GoInterface), RET (PairV #sl #err); ⌜err = interface.nil⌝ ∗
      ∃ (q : Loc) (ks : List GoString) (ls : List Loc),
      nsKeys F σ ns q ks ∗ ⌜ls.map (ptrObj k8s_io.api.apps.v1.ControllerRevision.ty) = ks.map (objAt σ.items)⌝ ∗
      (if ns = [] then iprop(True) else q ↦□ qMeta ns) ∗ sl ↦* ls ∗
      □ ([∗list] l ∈ ls, OK (ptrObj k8s_io.api.apps.v1.ControllerRevision.ty l)) ∗ tsReader ts γ OK Fam }}

end spec

end appslisters
end EtcdGrove
end Perennial

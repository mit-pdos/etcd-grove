/-
`nodeLister.List` (`listers/core/v1/node.go`, promoted from the embedded
`listers.ResourceIndexer[*v1.Node]`): the generic lister's `List`. Lean-first.
-/
module

public import Spec.k8s_io.client_go.listers.ResourceIndexer__List
public import GeneratedProof.k8s_io.client_go.listers.core.v1

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace corelisters

open Iris Iris.BI cache listers k8s_io.client_go.listers.core.v1

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.listers.core.v1.Assumptions]
variable [package_sem' : k8s_io.client_go.listers.Assumptions]

/-- **`l.List`** for the Node lister `l` (a `*nodeLister`) over the cache `ca`, not namespaced: `ResourceIndexer.List`'s spec at `X = v1.Node`. -/
abbrev nodeLister.List.spec : Prop :=
  ∀ (ca ts : Loc) (γ : TsNames) (OK : GoInterface → IProp GF) (Fam : Nat → Fn GF)
    (kf : GoFunc) (res : k8s_io.apimachinery.pkg.runtime.schema.GroupResource) (l : Loc)
    (sel : GoInterface) (F : Fn GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.listers.core.v1 ∗ isCache ca ts γ OK Fam kf ∗
      tsReader ts γ OK Fam ∗ typedOK OK k8s_io.api.core.v1.Node.ty ∗ everySel sel ∗ qOk OK ([] : GoString) ∗
      l.[nodeLister, go!"ResourceIndexer"] ↦□ riVal ca res [] }}
  <<{ ∀∀ σ, storeSt γ σ ∗
      ⌜noNil σ.items ∧ (([] : GoString) ≠ [] → St.fns Fam σ !! go!"namespace" = some F)⌝ }>>
    (App (Val (l @!! go.GoType.PointerType nodeLister.ty @!! go!"List")) (Val #sel))
    @@ ∅
  <<{ storeSt γ σ ∗ ⌜noNil σ.items ∧ (([] : GoString) ≠ [] → St.fns Fam σ !! go!"namespace" = some F)⌝ }>>
  {{ (sl : GoSlice) (err : GoInterface), RET (PairV #sl #err); ⌜err = interface.nil⌝ ∗
      ∃ (q : Loc) (ks : List GoString) (ls : List Loc),
      nsKeys F σ ([] : GoString) q ks ∗ ⌜ls.map (ptrObj k8s_io.api.core.v1.Node.ty) = ks.map (objAt σ.items)⌝ ∗
      (if ([] : GoString) = [] then iprop(True) else q ↦□ qMeta ([] : GoString)) ∗ sl ↦* ls ∗
      □ ([∗list] l ∈ ls, OK (ptrObj k8s_io.api.core.v1.Node.ty l)) ∗ tsReader ts γ OK Fam }}

end spec

end corelisters
end EtcdGrove
end Perennial

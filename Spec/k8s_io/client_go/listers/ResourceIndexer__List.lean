/-
`ResourceIndexer[T].List(selector)` (`generic_helpers.go:48`): the lister namespace's objects (all
objects for `""`). Lean-first.
-/
module

public import Proof.k8s_io.client_go.listers.Defs
public import Spec.k8s_io.client_go.tools.cache.ListAllByNamespace

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace listers

open Iris Iris.BI cache k8s_io.client_go.listers

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.listers.Assumptions]

/-- **`l.List(sel)`** for the lister `l` over the cache `ca` (`riVal ca res ns`), logically atomic
(a reader), for a selector that selects everything, a store of `*X` objects without `nil` items
and, for a namespace, its namespace indexer `F`: no error, and the objects of the store at the
linearization point that `ListAllByNamespace` visits (`nsKeys`), as their pointers `ls`, in some
order. -/
abbrev ResourceIndexer.List.spec : Prop :=
  ∀ (X : go.GoType) (ca ts : Loc) (γ : TsNames) (OK : GoInterface → IProp GF) (Fam : Nat → Fn GF)
    (kf : GoFunc) (res : k8s_io.apimachinery.pkg.runtime.schema.GroupResource) (ns : GoString)
    (sel : GoInterface) (F : Fn GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.listers ∗ isCache ca ts γ OK Fam kf ∗
      tsReader ts γ OK Fam ∗ typedOK OK X ∗ everySel sel ∗ qOk OK ns }}
  <<{ ∀∀ σ, storeSt γ σ ∗
      ⌜noNil σ.items ∧ (ns ≠ [] → St.fns Fam σ !! go!"namespace" = some F)⌝ }>>
    (App (Val #(methods (ResourceIndexer.ty (go.GoType.PointerType X)) go!"List"
      #(riVal ca res ns))) (Val #sel))
    @@ ∅
  <<{ storeSt γ σ ∗ ⌜noNil σ.items ∧ (ns ≠ [] → St.fns Fam σ !! go!"namespace" = some F)⌝ }>>
  {{ (sl : GoSlice) (err : GoInterface), RET (PairV #sl #err); ⌜err = interface.nil⌝ ∗
      ∃ (q : Loc) (ks : List GoString) (ls : List Loc),
      nsKeys F σ ns q ks ∗ ⌜ls.map (ptrObj X) = ks.map (objAt σ.items)⌝ ∗
      (if ns = [] then iprop(True) else q ↦□ qMeta ns) ∗ sl ↦* ls ∗
      □ ([∗list] l ∈ ls, OK (ptrObj X l)) ∗ tsReader ts γ OK Fam }}

end spec

end listers
end EtcdGrove
end Perennial

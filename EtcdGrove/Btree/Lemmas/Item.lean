/-
Lemmas for the non-generic API (`BTree` of `Item`s).
-/
import EtcdGrove.Btree.Item

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Btree

open Iris Iris.BI Iris.ProofMode github_com.google.btree

section lemmas
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.google.btree.Assumptions]

/-- After initialization, `itemLess` holds a function that behaves as `Item.Less`. -/
theorem isInit_access :
    isPkgInit (PROP := IProp GF) pkg_id.github_com.google.btree ⊢ isInit (GF := GF) :=
  isPkgInit_access (PROP := IProp GF) pkg_id.github_com.google.btree

/-- The closure stored in `itemLess` decides the order of items whose `Less` methods
do. -/
theorem isLess_itemLess {K : Type} (o : ItemOrder GF GoInterface K) (f : GoFunc) :
    isItemLessFn f ∗ isItemOrderLess o ⊢ isLess o f := by
  iintro ⟨#Hf, #Ho⟩
  unfold isLess
  iintro %a %b %ka %kb
  iintro !> %Φ Hpre HΦ
  unfold isItemLessFn
  iapply Hf
  unfold isItemOrderLess
  iapply Ho $$ Hpre HΦ

end lemmas

end Btree
end EtcdGrove
end Perennial

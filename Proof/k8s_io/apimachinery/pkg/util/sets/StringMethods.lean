/-
`sets.String` (the deprecated string set, `string.go`, translated with its bodies): `NewString()`
and the `*String` method set's wrappers of `String`'s `Has` and `Insert` (which convert to the
generic `Set[string]`, `cast`, and call its method), from the generic `Set[T]`'s specs (`X_of`,
hypotheses). Lean-first; for `field.ErrorList.ToAggregate`, which deduplicates its errors' messages
with one.
-/
module

public import Spec.k8s_io.apimachinery.pkg.util.sets.Set__Has
public import Spec.k8s_io.apimachinery.pkg.util.sets.Set__Insert
public import Spec.k8s_io.apimachinery.pkg.util.sets.New

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace sets

open Iris Iris.BI Iris.ProofMode k8s_io.apimachinery.pkg.util.sets

section wps
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apimachinery.pkg.util.sets.Assumptions]

/-- `sets.NewString()` (no items): a new empty set. -/
theorem wp_NewString_nil_of (wp_New : New.spec (GF := GF) (hG := hG)) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apimachinery.pkg.util.sets }}
      (App (Val (@! NewString)) (Val #slice.nil))
    {{ (r : Loc), RET #r; r ↦$ (∅ : GMap GoString Elem) }} := by
  wp_start
  ihave Hn : (slice.nil ↦* ([] : List GoString) : IProp GF) $$ []
  · iapply ownSlice_nil
  wp_auto
  wp_apply (wp_New (K := GoString) (T := go.string) slice.nil (DFrac.own 1) []) $$ [$Hn] as %r ⟨Hr, -⟩
  simp only [show insertAll (∅ : GMap GoString Elem) [] = ∅ from rfl]
  iapply HΦ
  iexact Hr

/-- `(*String).Has` on the set `*l`. -/
theorem String.wp_ptr_Has_of (wp_Has : Set.Has.spec (GF := GF) (hG := hG))
    (l : Loc) (dl : DFrac) (m : Loc) (dq : DFrac) (s : GMap GoString Elem) (k : GoString) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apimachinery.pkg.util.sets ∗
        l ↦{dl} (m : k8s_io.apimachinery.pkg.util.sets.String) ∗ m ↦${dq} s }}
      (App (Val (l @!! go.GoType.PointerType String.ty @!! go!"Has")) (Val #k))
    {{ RET #(decide ((s !! k).isSome)); l ↦{dl} (m : k8s_io.apimachinery.pkg.util.sets.String) ∗
        m ↦${dq} s }} := by
  wp_start as ⟨Hl, Hm⟩
  wp_auto
  simp only [method_unfold]
  wp_auto
  rw [func_unfold]
  wp_auto
  wp_apply (wp_Has (T := go.string)) $$ [$Hm] as Hm
  iapply HΦ; iframe

/-- `(*String).Insert` on the set `*l`. -/
theorem String.wp_ptr_Insert_of (wp_Insert : Set.Insert.spec (GF := GF) (hG := hG))
    (l : Loc) (dl : DFrac) (m : Loc) (s : GMap GoString Elem) (sl : GoSlice) (dq : DFrac)
    (ks : List GoString) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apimachinery.pkg.util.sets ∗
        l ↦{dl} (m : k8s_io.apimachinery.pkg.util.sets.String) ∗ m ↦$ s ∗ sl ↦*{dq} ks }}
      (App (Val (l @!! go.GoType.PointerType String.ty @!! go!"Insert")) (Val #sl))
    {{ RET #m; l ↦{dl} (m : k8s_io.apimachinery.pkg.util.sets.String) ∗ m ↦$ insertAll s ks ∗
        sl ↦*{dq} ks }} := by
  wp_start as ⟨Hl, Hm, Hsl⟩
  wp_auto
  simp only [method_unfold]
  wp_auto
  rw [func_unfold]
  wp_auto
  wp_apply (wp_Insert (T := go.string)) $$ [$Hm $Hsl] as ⟨Hm, Hsl⟩
  iapply HΦ; iframe

end wps

end sets
end EtcdGrove
end Perennial

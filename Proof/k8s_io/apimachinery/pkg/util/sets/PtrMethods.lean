/-
The `*Set[T]` method set's wrappers of `Set[T]`'s value methods (Go calls `s.Has(x)` on an
addressable `s` through them: goose's `ptr_Has_unfold`, ...): the value method on `*l`, from its
spec (`X_of`, a hypothesis). Lean-first; for client-go's work queue, which calls them on its
struct's fields.
-/
module

public import Spec.k8s_io.apimachinery.pkg.util.sets.Set__Has
public import Spec.k8s_io.apimachinery.pkg.util.sets.Set__Insert
public import Spec.k8s_io.apimachinery.pkg.util.sets.Set__Delete
public import Spec.k8s_io.apimachinery.pkg.util.sets.Set__Len

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace sets

open Iris Iris.BI Iris.ProofMode k8s_io.apimachinery.pkg.util.sets

section wps
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apimachinery.pkg.util.sets.Assumptions]
variable {K : Type} [ZeroVal K] [DecidableEq K] [go.IntoValInj K] [TypedPointsto (GF := GF) K]
  {T : go.GoType} [IntoValTyped (GF := GF) K T]

/-- `(*Set[T]).Has` on the set `*l`. -/
theorem Set.wp_ptr_Has_of (wp_Has : Set.Has.spec (GF := GF) (hG := hG))
    (l : Loc) (dl : DFrac) (m : Loc) (dq : DFrac) (s : GMap K Elem) (k : K)
    [SafeMapKey (GF := GF) T k] :
    {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apimachinery.pkg.util.sets ∗
        l ↦{dl} (m : Set' K) ∗ m ↦${dq} s }}
      (App (Val (l @!! go.GoType.PointerType (Set'.ty T) @!! go!"Has")) (Val #k))
    {{ RET #(decide ((s !! k).isSome)); l ↦{dl} (m : Set' K) ∗ m ↦${dq} s }} := by
  wp_start as ⟨Hl, Hm⟩
  wp_auto
  wp_apply wp_Has $$ [$Hm] as Hm
  iapply HΦ; iframe

/-- `(*Set[T]).Len` on the set `*l`. -/
theorem Set.wp_ptr_Len_of (wp_Len : Set.Len.spec (GF := GF) (hG := hG))
    (l : Loc) (dl : DFrac) (m : Loc) (dq : DFrac) (s : GMap K Elem) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apimachinery.pkg.util.sets ∗
        l ↦{dl} (m : Set' K) ∗ m ↦${dq} s }}
      (App (Val (l @!! go.GoType.PointerType (Set'.ty T) @!! go!"Len")) (Val #()))
    {{ RET #(W64 (GMap.size s)); l ↦{dl} (m : Set' K) ∗ m ↦${dq} s }} := by
  wp_start as ⟨Hl, Hm⟩
  wp_auto
  wp_apply wp_Len (T := T) $$ [$Hm] as Hm
  iapply HΦ; iframe

/-- `(*Set[T]).Insert` on the set `*l`. -/
theorem Set.wp_ptr_Insert_of (wp_Insert : Set.Insert.spec (GF := GF) (hG := hG))
    [∀ k : K, SafeMapKey (GF := GF) T k]
    (l : Loc) (dl : DFrac) (m : Loc) (s : GMap K Elem) (sl : GoSlice) (dq : DFrac) (ks : List K) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apimachinery.pkg.util.sets ∗
        l ↦{dl} (m : Set' K) ∗ m ↦$ s ∗ sl ↦*{dq} ks }}
      (App (Val (l @!! go.GoType.PointerType (Set'.ty T) @!! go!"Insert")) (Val #sl))
    {{ RET #m; l ↦{dl} (m : Set' K) ∗ m ↦$ insertAll s ks ∗ sl ↦*{dq} ks }} := by
  wp_start as ⟨Hl, Hm, Hsl⟩
  wp_auto
  wp_apply wp_Insert $$ [$Hm $Hsl] as ⟨Hm, Hsl⟩
  iapply HΦ; iframe

/-- `(*Set[T]).Delete` on the set `*l`. -/
theorem Set.wp_ptr_Delete_of (wp_Delete : Set.Delete.spec (GF := GF) (hG := hG))
    [∀ k : K, SafeMapKey (GF := GF) T k]
    (l : Loc) (dl : DFrac) (m : Loc) (s : GMap K Elem) (sl : GoSlice) (dq : DFrac) (ks : List K) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apimachinery.pkg.util.sets ∗
        l ↦{dl} (m : Set' K) ∗ m ↦$ s ∗ sl ↦*{dq} ks }}
      (App (Val (l @!! go.GoType.PointerType (Set'.ty T) @!! go!"Delete")) (Val #sl))
    {{ RET #m; l ↦{dl} (m : Set' K) ∗ m ↦$ deleteAll s ks ∗ sl ↦*{dq} ks }} := by
  wp_start as ⟨Hl, Hm, Hsl⟩
  wp_auto
  wp_apply wp_Delete $$ [$Hm $Hsl] as ⟨Hm, Hsl⟩
  iapply HΦ; iframe

end wps

end sets
end EtcdGrove
end Perennial

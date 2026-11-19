/-
**`value`'s freelists** (structured-merge-diff v7.0.0): the specs of the generic
`(*freelist[T]).allocate`/`free` over `freelistOwn` (`Objects.lean`), which the `freelistAllocator`
methods' proofs use (the Draft gave the generic methods no spec files of their own: they are
proved here, once, for every `T` whose elements are pointers). A defs-tier module.
-/
module

public import Proof.sigs_k8s_io.structured_merge_diff.v7.value.LawProofs
import all Proof.sigs_k8s_io.structured_merge_diff.v7.value.Defs
import all Proof.sigs_k8s_io.structured_merge_diff.v7.value.Objects

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace smd

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open sigs_k8s_io.structured_merge_diff.v7

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : value.Assumptions]

theorem valueSepL_append {α : Type} (f : α → IProp GF) (xs ys : List α) :
    valueSepL f (xs ++ ys) ⊣⊢ valueSepL f xs ∗ valueSepL f ys := by
  induction xs with
  | nil => simp only [valueSepL, List.nil_append, List.foldr_nil]; exact true_sep.symm
  | cons x xs ih =>
    simp only [valueSepL, List.cons_append, List.foldr_cons] at ih ⊢
    exact (sep_congr .rfl ih).trans sep_assoc.symm

theorem valueSepL_single {α : Type} (f : α → IProp GF) (x : α) :
    valueSepL f [x] ⊣⊢ f x := by
  simp only [valueSepL, List.foldr_cons, List.foldr_nil]; exact sep_true

theorem isAlloc_fl_elim (p : Loc) :
    isAlloc (GF := GF) (interface.mkOk (go.GoType.PointerType value.freelistAllocator.ty) #p) ⊢
      ∃ fa : value.freelistAllocator, p ↦□ fa ∗
        freelistOwn fa.valueUnstructured' wrapperOwn ∗ freelistOwn fa.listUnstructuredRange' rangeOwn := by
  iintro Ha
  iunfold isAlloc at Ha
  icases Ha with (⟨%p', %h⟩ | ⟨%p', %fa, %h, #Hp, H1, H2⟩)
  · simp [value.heapAllocator.ty, value.freelistAllocator.ty] at h
  · simp [intoVal_eq_iff] at h
    subst h
    iexists fa
    iframe
    iexact Hp

theorem isAlloc_fl_intro (p : Loc) (fa : value.freelistAllocator) :
    p ↦□ fa ∗ freelistOwn (GF := GF) fa.valueUnstructured' wrapperOwn ∗
      freelistOwn fa.listUnstructuredRange' rangeOwn ⊢
      isAlloc (GF := GF) (interface.mkOk (go.GoType.PointerType value.freelistAllocator.ty) #p) := by
  iintro ⟨#Hp, H1, H2⟩
  iunfold isAlloc
  iright
  iexists p, fa
  iframe
  isplitr
  · ipureintro; rfl
  · iexact Hp

theorem wp_freelist_allocate (E : go.GoType) (fp : Loc) (own : Loc → IProp GF) :
    {{ freelistOwn fp own }}
      (App (Val #(methods (go.GoType.PointerType (value.freelist.ty (go.GoType.PointerType E)))
        go!"allocate" #fp)) (Val #()))
    {{ (q : Loc), RET #q; freelistOwn fp own ∗ own q }} := by
  wp_start as Hf
  iunfold freelistOwn at Hf
  icases Hf with ⟨%fl, Hfp, ⟨%qs, Hs, Hcap, Hown⟩, #Hnew⟩
  ihave %Hlen := ownSlice_len $$ Hs
  wp_auto
  wp_if_destruct
  · obtain ⟨q, hq⟩ : ∃ q, qs[qs.length - 1]? = some q :=
      ⟨_, List.getElem?_eq_getElem (by word)⟩
    have hk : 0 ≤ sint.Z (fl.list'.len - W64 1) ∧ sint.Z (fl.list'.len - W64 1) < sint.Z fl.list'.len := by
      constructor <;> word
    simp only [hk, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index fl.list' _ qs (DFrac.own 1) q (by word) $$ [Hs] as Hs
    · iframe; ipureintro
      rw [← hq]; congr 1; word
    ihave %Hwf := ownSliceCap_wf $$ Hcap
    have hb : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z (fl.list'.len - W64 1) ∧
        sint.Z (fl.list'.len - W64 1) ≤ sint.Z fl.list'.cap := by
      refine ⟨by word, by word, by word⟩
    simp only [hb, _root_.and_self, ↓reduceIte]
    ihave ⟨-, Hs', Hcap'⟩ := ownSlice_slice_with_cap (W64 0) (fl.list'.len - W64 1) fl.list' qs
      ⟨by word, by word, by word⟩ $$ [Hs Hcap]
    · iframe
    have hqs : qs = qs.take (qs.length - 1) ++ [q] := by
      have hn : qs ≠ [] := by rintro rfl; simp at hq
      have hl : qs.getLast hn = q := by
        rw [List.getLast_eq_getElem]
        exact Option.some_inj.mp (by rw [← hq, List.getElem?_eq_getElem])
      calc qs = qs.dropLast ++ [qs.getLast hn] := (List.dropLast_concat_getLast hn).symm
        _ = _ := by rw [List.dropLast_eq_take, hl]
    have hsplit : valueSepL own qs ⊢ valueSepL own (qs.take (qs.length - 1)) ∗ own q := by
      conv => lhs; rw [hqs]
      exact (valueSepL_append own _ _).1.trans (sep_mono .rfl (valueSepL_single own q).1)
    ihave ⟨Hown, Hq⟩ := hsplit $$ Hown
    wp_auto
    iapply HΦ
    iframe
    iunfold freelistOwn
    iexists _
    iframe
    · have he : subslice (sint.nat (W64 0)) (sint.nat (fl.list'.len - W64 1)) qs =
          qs.take (qs.length - 1) := by
        simp only [subslice]
        rw [show sint.nat (W64 0) = 0 by rfl, List.drop_zero]
        congr 1; word
      rw [← he]
      isplitl
      · iexact Hs'
      · iexact Hnew
  · wp_apply Hnew as %q Hq
    iapply HΦ
    iframe
    iunfold freelistOwn
    iexists fl
    iframe
    iexact Hnew

theorem wp_freelist_free (E : go.GoType) (fp : Loc) (own : Loc → IProp GF) (q : Loc) :
    {{ freelistOwn fp own ∗ own q }}
      (App (Val #(methods (go.GoType.PointerType (value.freelist.ty (go.GoType.PointerType E)))
        go!"free" #fp)) (Val #q))
    {{ RET #(); freelistOwn fp own }} := by
  wp_start as ⟨Hf, Hq⟩
  iunfold freelistOwn at Hf
  icases Hf with ⟨%fl, Hfp, ⟨%qs, Hs, Hcap, Hown⟩, #Hnew⟩
  wp_auto
  wp_if_destruct
  · wp_apply (wp_slice_literal (V := Loc) [q])
    isplitr
    · ipureintro; rfl
    iintro %osl ⟨Hosl, -⟩
    (try wp_auto)
    wp_apply (wp_slice_append (V := Loc)) $$ [$Hs $Hcap $Hosl] as %s' ⟨Hs, Hcap, -⟩
    (try wp_auto)
    iapply HΦ
    iunfold freelistOwn
    iexists _
    iframe
    isplitl
    · iapply (valueSepL_append own qs [q]).2
      iframe
      iapply (valueSepL_single own q).2
      iexact Hq
    · iexact Hnew
  · iapply HΦ
    iunfold freelistOwn
    iexists fl
    iframe
    iexact Hnew

end lemmas

end smd
end EtcdGrove
end Perennial

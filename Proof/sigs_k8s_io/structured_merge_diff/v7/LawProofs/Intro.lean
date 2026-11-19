/-
**The root laws' fraction, introduction and elimination parts, proved** (`v7/Laws.lean`): the
lent wrapper `isValF`, the client literals (`isIface_*`, `isFieldList_intro`, `isPath_intro`,
`isPaths_*`, `isConflicts_intro`, `isUpdater_intro`, `isTypeRef_intro`,
`isIdentityConverter_intro`), and the eliminations `isTV_*`, `isMF_sorted`.

Prove phase (2026-11-19, notes/smd-plan.md).
-/
module

public import Proof.sigs_k8s_io.structured_merge_diff.v7.LawProofs.Persist
import all Proof.sigs_k8s_io.structured_merge_diff.v7.value.Defs
import all Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Defs
import all Proof.sigs_k8s_io.structured_merge_diff.v7.schema.Defs
import all Proof.sigs_k8s_io.structured_merge_diff.v7.merge.Defs
import all Proof.sigs_k8s_io.structured_merge_diff.v7.typed.Defs

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace smd

open Iris Iris.BI Iris.ProofMode
open sigs_k8s_io.structured_merge_diff.v7

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

open LawProofs

/-! ## `isValF` -/

theorem isValF_split_law_holds : isValF_split.law (GF := GF) := fun v dq1 dq2 x => by
  unfold isValF
  constructor
  · iintro ⟨%p, %i, %hv, Hp, #Hi⟩
    icases ((typedPointsto_dfractional _ _).dfractional dq1 dq2).1 $$ Hp with ⟨H1, H2⟩
    isplitl [H1]
    · iexists p, i; iframe #; iframe; ipureintro; exact hv
    · iexists p, i; iframe #; iframe; ipureintro; exact hv
  · iintro ⟨⟨%p, %i, %hv, H1, #Hi⟩, ⟨%p', %i', %hv', H2, #Hi'⟩⟩
    rw [hv, interface_mkOk_inj, intoVal_eq_iff] at hv'
    obtain ⟨-, rfl⟩ := hv'
    ihave %hii := typedPointsto_agree_wand _ _ _ _ _ $$ H1 H2
    cases hii
    iexists p, i
    isplitr
    · ipureintro; exact hv
    isplitl [H1 H2]
    · iapply ((typedPointsto_dfractional _ _).dfractional dq1 dq2).2
      iframe
    · iexact Hi

theorem isValF_persist_law_holds : isValF_persist.law (GF := GF) := fun v dq x => by
  unfold isVal
  unfold isValF
  iintro ⟨%p, %i, %hv, Hp, #Hi⟩
  imod (typedPointsto_dfractional _ _).dfractional_persist dq $$ Hp with #Hp
  imodintro
  iexists p, i
  iframe #
  ipureintro; exact hv

/-! ## Scalars, lists of literals -/

theorem isIface_scalar_law_holds : isIface_scalar.law (GF := GF) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intros <;> (unfold isIface; iintro _; ipureintro; rfl)

theorem LawProofs.sepL_nil {α : Type} (f : α → IProp GF) : sepL f [] = iprop(True) := rfl
theorem LawProofs.sepL_cons {α : Type} (f : α → IProp GF) (a : α) (xs : List α) :
    sepL f (a :: xs) = iprop(f a ∗ sepL f xs) := rfl

theorem LawProofs.isIfaceL_of_sepL : ∀ (xs : List GoInterface) (vs : List UVal), xs.length = vs.length →
    sepL (fun xv => isIface (GF := GF) xv.1 xv.2) (xs.zip vs) ⊢ isIfaceL xs vs
  | [], [], _ => by unfold isIfaceL; iintro _; ipureintro; trivial
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | x :: xs, v :: vs, h => by
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h
      simp only [List.zip_cons_cons, sepL_cons]
      unfold isIfaceL
      iintro ⟨H, Hr⟩
      iframe
      iapply isIfaceL_of_sepL xs vs h
      iexact Hr

theorem isIface_list_law_holds : isIface_list.law (GF := GF) := fun sl xs vs h => by
  iintro #Hs Hl
  ihave Hl := isIfaceL_of_sepL xs vs h $$ Hl
  unfold isIface
  iexists sl, xs
  iframe; iframe #
  ipureintro; rfl

theorem LawProofs.isFieldsL_of_sepL : ∀ (fs : List value.Field) (fl : FieldList), fs.length = fl.length →
    sepL (fun ff => iprop(⌜ff.1.Name' = ff.2.1⌝ ∗ isVal (GF := GF) ff.1.Value' ff.2.2)) (fs.zip fl) ⊢
      isFieldsL fs fl
  | [], [], _ => by unfold isFieldsL; iintro _; ipureintro; trivial
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | f :: fs, (n, x) :: fl, h => by
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h
      simp only [List.zip_cons_cons, sepL_cons]
      unfold isFieldsL
      iintro ⟨⟨%hn, H⟩, Hr⟩
      isplitr
      · ipureintro; exact hn
      iframe
      iapply isFieldsL_of_sepL fs fl h
      iexact Hr

theorem isFieldList_intro_law_holds : isFieldList_intro.law (GF := GF) := fun s fs fl h => by
  iintro #Hs Hl
  ihave Hl := isFieldsL_of_sepL fs fl h $$ Hl
  unfold isFieldList
  iexists fs
  iframe; iframe #

theorem LawProofs.isPEL_of_sepL : ∀ (es : List fieldpath.PathElement) (p : Path), es.length = p.length →
    sepL (fun ep => isPE (GF := GF) ep.1 ep.2) (es.zip p) ⊢ isPEL es p
  | [], [], _ => by unfold isPEL; iintro _; ipureintro; trivial
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | e :: es, pe :: p, h => by
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h
      simp only [List.zip_cons_cons, sepL_cons]
      unfold isPEL
      iintro ⟨H, Hr⟩
      iframe
      iapply isPEL_of_sepL es p h
      iexact Hr

theorem isPath_intro_law_holds : isPath_intro.law (GF := GF) := fun s es p h => by
  iintro #Hs Hl
  ihave Hl := isPEL_of_sepL es p h $$ Hl
  unfold isPath
  iexists es
  iframe; iframe #

theorem isPaths_nil_law_holds : isPaths_nil.law (GF := GF) := by
  unfold isPaths_nil.law isPaths; iintro _; ipureintro; trivial

theorem isPaths_cons_law_holds : isPaths_cons.law (GF := GF) := fun s ss p ps => by
  conv => lhs; unfold isPaths
  exact .rfl

theorem isPaths_length_law_holds : isPaths_length.law (GF := GF) := by
  intro ss
  induction ss with
  | nil =>
    intro ps
    cases ps with
    | nil => iintro _; ipureintro; rfl
    | cons _ _ => unfold isPaths; iintro %h; exact h.elim
  | cons s ss ih =>
    intro ps
    cases ps with
    | nil => unfold isPaths; iintro %h; exact h.elim
    | cons p ps =>
      unfold isPaths
      iintro ⟨_, H⟩
      ihave %h := ih ps $$ H
      ipureintro; simp [h]

theorem isPaths_app_law_holds : isPaths_app.law (GF := GF) := by
  intro ss
  induction ss with
  | nil =>
    intro ss' ps ps' h
    cases ps with
    | nil =>
      simp only [List.nil_append]
      conv => rhs; lhs; unfold isPaths
      constructor
      · iintro H; isplitr
        · ipureintro; trivial
        · iexact H
      · iintro ⟨_, H⟩; iexact H
    | cons _ _ => simp at h
  | cons s ss ih =>
    intro ss' ps ps' h
    cases ps with
    | nil => simp at h
    | cons p ps =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h
      simp only [List.cons_append]
      rw [isPaths.eq_2, isPaths.eq_2]
      constructor
      · iintro ⟨Hp, H⟩
        icases (ih ss' ps ps' h).1 $$ H with ⟨H1, H2⟩
        iframe
      · iintro ⟨⟨Hp, H1⟩, H2⟩
        iframe
        iapply (ih ss' ps ps' h).2
        iframe

theorem LawProofs.isConflictL_of_sepL : ∀ (xs : List merge.Conflict) (cs : List (GoString × Path)),
    xs.length = cs.length →
    sepL (fun xc => iprop(⌜xc.1.Manager' = xc.2.1⌝ ∗ isPath (GF := GF) xc.1.Path' xc.2.2)) (xs.zip cs) ⊢
      isConflictL xs cs
  | [], [], _ => by unfold isConflictL; iintro _; ipureintro; trivial
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | x :: xs, (m, p) :: cs, h => by
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h
      simp only [List.zip_cons_cons, sepL_cons]
      unfold isConflictL
      iintro ⟨⟨%hm, H⟩, Hr⟩
      isplitr
      · ipureintro; exact hm
      iframe
      iapply isConflictL_of_sepL xs cs h
      iexact Hr

theorem isConflicts_intro_law_holds : isConflicts_intro.law (GF := GF) := fun s xs cs h => by
  iintro #Hs Hl
  ihave Hl := isConflictL_of_sepL xs cs h $$ Hl
  unfold isConflicts
  iexists xs
  iframe; iframe #

theorem isUpdater_intro_law_holds : isUpdater_intro.law (GF := GF) := fun u cv igf igfl rion => by
  unfold isUpdater; exact .rfl

theorem isTypeRef_intro_law_holds : isTypeRef_intro.law (GF := GF) :=
  fun tr t h1 h2 h3 h4 h5 => by
  unfold isTypeRef
  iintro #H
  iframe #
  ipureintro; exact ⟨⟨h1, h2, h3⟩, h4, h5⟩

theorem isIdentityConverter_intro_law_holds : isIdentityConverter_intro.law (GF := GF) :=
  fun T v => by
  unfold isIdentityConverter
  iintro ⟨#H1, #H2⟩
  iexists T, v
  isplitr
  · ipureintro; rfl
  iframe #

/-! ## Eliminations -/

theorem isTV_conforms_law_holds : isTV_conforms.law (GF := GF) := fun p sc S t x => by
  unfold isTV
  iintro ⟨%v, %tr, _, _, _, _, %h⟩
  ipureintro; exact h.2

theorem isTV_schema_law_holds : isTV_schema.law (GF := GF) := fun p sc S t x => by
  unfold isTV
  iintro ⟨%v, %tr, _, _, _, #Hs, %h⟩
  iframe #
  ipureintro; exact h.1

theorem isMF_sorted_law_holds : isMF_sorted.law (GF := GF) := fun m mf => by
  unfold isMF
  iintro ⟨%M, _, %h, _⟩
  ipureintro; exact h.1

end laws
end smd
end EtcdGrove
end Perennial

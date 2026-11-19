/-
**The `schema` package's piece-view laws, proved** (`schema/Laws.lean`): persistence, the
type-reference and atom readings, the field eliminations, and the pure premises from `Schema.WF`.

Prove phase (2026-11-19, notes/smd-plan.md).
-/
module

public import Proof.sigs_k8s_io.structured_merge_diff.v7.schema.Laws
public import Proof.sigs_k8s_io.structured_merge_diff.v7.LawProofs.Persist
import all Proof.sigs_k8s_io.structured_merge_diff.v7.schema.Defs

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace smd

open Iris Iris.BI Iris.ProofMode
open sigs_k8s_io.structured_merge_diff.v7
open LawProofs

/-- The zero atom is the atom with no pointer set. -/
theorem LawProofs.atomZero_iff [GooseExts] (a : schema.Atom) : atomZero a ↔ a = zero_val schema.Atom := by
  cases a
  simp only [atomZero, zero_val, zeroValDef]
  constructor
  · rintro ⟨rfl, rfl, rfl⟩; rfl
  · intro h; cases h; exact ⟨rfl, rfl, rfl⟩

theorem LawProofs.typeRef_zero_iff [GooseExts] (tr : schema.TypeRef) :
    (tr.NamedType' = null ∧ atomZero tr.Inlined' ∧ tr.ElementRelationship' = null ∧
      tr.Nullable' = false) ↔ tr = zero_val schema.TypeRef := by
  cases tr with
  | mk n a r b =>
    rw [atomZero_iff]
    simp only [zero_val, zeroValDef]
    constructor
    · rintro ⟨rfl, rfl, rfl, rfl⟩; rfl
    · intro h; cases h; exact ⟨rfl, rfl, rfl, rfl⟩

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

theorem isTypeRefOpt_persistent_law_holds : isTypeRefOpt_persistent.law (GF := GF) :=
  fun _ _ => pers_box
theorem isAtomOpt_persistent_law_holds : isAtomOpt_persistent.law (GF := GF) :=
  fun _ _ => pers_box
theorem isListRep_persistent_law_holds : isListRep_persistent.law (GF := GF) :=
  fun _ _ _ _ => pers_box
theorem isMapRep_persistent_law_holds : isMapRep_persistent.law (GF := GF) :=
  fun _ _ _ _ => pers_box
theorem isStructField_persistent_law_holds : isStructField_persistent.law (GF := GF) :=
  fun _ _ => pers_box

theorem isTypeRefOpt_some_law_holds : isTypeRefOpt_some.law (GF := GF) := fun tr t => by
  unfold isTypeRefOpt; exact .rfl

theorem isTypeRefOpt_none_law_holds : isTypeRefOpt_none.law (GF := GF) := fun tr => by
  unfold isTypeRefOpt
  rw [typeRef_zero_iff]; exact .rfl

theorem isTypeRef_elim_law_holds : isTypeRef_elim.law (GF := GF) := fun tr t => by
  unfold isTypeRef
  iintro ⟨#Hn, %h⟩; obtain ⟨hz, hr, hn⟩ := h
  isplitl
  · iexact Hn
  · ipureintro; exact ⟨(atomZero_iff _).1 hz, hr, hn⟩

theorem isAtomOpt_none_law_holds : isAtomOpt_none.law (GF := GF) := fun a => by
  unfold isAtomOpt
  rw [atomZero_iff]; exact .rfl

theorem isAtomOpt_scalar_law_holds : isAtomOpt_scalar.law (GF := GF) := fun a s => by
  unfold isAtomOpt isAtom; exact .rfl

theorem isAtomOpt_list_law_holds : isAtomOpt_list.law (GF := GF) := fun a e rel ks => by
  unfold isAtomOpt isAtom; exact .rfl

theorem isAtomOpt_map_law_holds : isAtomOpt_map.law (GF := GF) := fun a fs e rel => by
  unfold isAtomOpt isAtom isMapRep; exact .rfl

theorem isListRep_elim_law_holds : isListRep_elim.law (GF := GF) := fun l e rel ks => by
  unfold isListRep; exact .rfl

theorem LawProofs.isFields_elim : ∀ (sfs : List schema.StructField) (fs : List (GoString × TypeRef)),
    isFields (GF := GF) sfs fs ⊢ ⌜sfs.length = fs.length⌝ ∗
      □ (∀ (i : Nat) sf f, ⌜sfs[i]? = some sf ∧ fs[i]? = some f⌝ -∗ isStructField sf f)
  | [], [] => by
      iintro _
      isplitl
      · ipureintro; rfl
      · imodintro; iintro %i %sf %f %h; simp at h
  | [], _ :: _ => by unfold isFields; iintro %h; exact h.elim
  | _ :: _, [] => by unfold isFields; iintro %h; exact h.elim
  | sf0 :: sfs, f0 :: fs => by
      unfold isFields
      iintro ⟨#H0, Hr⟩
      ihave ⟨%hl, #Hr⟩ := isFields_elim sfs fs $$ Hr
      isplitl
      · ipureintro; simp [hl]
      · imodintro
        iintro %i %sf %f %h; obtain ⟨h1, h2⟩ := h
        cases i with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at h1 h2
          subst h1; subst h2; iexact H0
        | succ i =>
          simp only [List.getElem?_cons_succ] at h1 h2
          iapply Hr; ipureintro; exact ⟨h1, h2⟩

theorem isMapRep_elim_law_holds : isMapRep_elim.law (GF := GF) := fun m fs e rel => by
  unfold isMapRep mapRep
  iintro ⟨%fsl, %sfs, %us, %etv, #Hf, #Hs, Hfs, #Hu, %hu, #He, #Het, #Hr, _⟩
  ihave ⟨%hl, #Hfs⟩ := isFields_elim sfs fs $$ Hfs
  subst hu
  iexists fsl, sfs, etv
  iframe #
  ipureintro; exact hl

/-- A reference of the scope has no element-relationship override. -/
theorem LawProofs.isTypeRefOpt_er (tr : schema.TypeRef) (ot : Option TypeRef) :
    isTypeRefOpt (GF := GF) tr ot ⊢ ⌜tr.ElementRelationship' = null⌝ := by
  cases ot with
  | none => unfold isTypeRefOpt; iintro %h; ipureintro; exact h.2.2.1
  | some t => unfold isTypeRefOpt isTypeRef; iintro ⟨_, %h⟩; ipureintro; exact h.2.1

theorem isStructField_elim_law_holds : isStructField_elim.law (GF := GF) := fun sf f => by
  unfold isStructField; exact .rfl

end laws

/-! ## Pure laws -/

theorem LawProofs.lookupKV_mem {α : Type} {k : GoString} : ∀ {xs : List (GoString × α)} {v : α},
    lookupKV k xs = some v → (k, v) ∈ xs
  | [], _, h => by simp [lookupKV] at h
  | (k', v') :: rest, v, h => by
      unfold lookupKV at h
      split at h
      · cases h; subst_vars; exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (lookupKV_mem h)

theorem Schema.WF_types_nodup_law_holds : Schema.WF_types_nodup.law := fun S h => by
  unfold Schema.WF at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1

theorem Schema.WF_fields_nodup_law_holds : Schema.WF_fields_nodup.law := fun S n fs e rel h hf => by
  unfold Schema.WF at h
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  have hm := lookupKV_mem (hf : lookupKV n S.types = _)
  have := h.2 _ hm
  simp only [Atom.wf, Bool.and_eq_true, decide_eq_true_eq] at this
  exact this.1.1

end smd
end EtcdGrove
end Perennial

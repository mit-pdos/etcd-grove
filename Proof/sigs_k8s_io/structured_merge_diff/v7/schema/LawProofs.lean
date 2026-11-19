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

/-! ## The lazy indexes' contents (`lastNamed`) -/

theorem LawProofs.lastNamed_foldl {α : Type} (name : α → GoString) (n : GoString) :
    ∀ (xs : List α) (acc : Option α),
    xs.foldl (fun acc x => if name x = n then some x else acc) acc =
      (xs.foldl (fun acc x => if name x = n then some x else acc) none).or acc
  | [], acc => by simp
  | x :: xs, acc => by
      simp only [List.foldl_cons]
      rw [LawProofs.lastNamed_foldl name n xs, LawProofs.lastNamed_foldl name n xs
        (if name x = n then some x else none)]
      by_cases h : name x = n <;> simp [h]

theorem LawProofs.lastNamed_nil {α : Type} (name : α → GoString) (n : GoString) :
    lastNamed name n ([] : List α) = none := by unfold lastNamed; rfl

theorem LawProofs.lastNamed_cons {α : Type} (name : α → GoString) (n : GoString) (x : α)
    (xs : List α) :
    lastNamed name n (x :: xs) = (lastNamed name n xs).or (if name x = n then some x else none) := by
  unfold lastNamed
  simp only [List.foldl_cons]
  rw [LawProofs.lastNamed_foldl]

theorem LawProofs.lastNamed_snoc {α : Type} (name : α → GoString) (n : GoString) (xs : List α)
    (x : α) :
    lastNamed name n (xs ++ [x]) = if name x = n then some x else lastNamed name n xs := by
  unfold lastNamed
  simp [List.foldl_append]

theorem LawProofs.lookupKV_none_of_not_mem {α : Type} {n : GoString} :
    ∀ {xs : List (GoString × α)}, n ∉ xs.map (·.1) → lookupKV n xs = none
  | [], _ => rfl
  | (k, v) :: rest, h => by
      simp only [List.map_cons, List.mem_cons, not_or] at h
      unfold lookupKV
      simp only [Ne.symm h.1, ite_false]
      exact LawProofs.lookupKV_none_of_not_mem h.2

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
  iintro ⟨%_, %fsl, %sfs, %us, %etv, #Hf, #Hs, Hfs, #Hu, %hu, #He, #Het, #Hr, _⟩
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

theorem isMapRep_nonnull_law_holds : isMapRep_nonnull.law (GF := GF) := fun m fs e rel => by
  unfold isMapRep mapRep
  iintro ⟨%h, -⟩
  ipureintro; exact h

theorem isListRep_nonnull_law_holds : isListRep_nonnull.law (GF := GF) := fun l e rel ks => by
  unfold isListRep
  iintro ⟨%v, %ksl, #Hl, -⟩
  iapply typedPointsto_not_null
  iexact Hl

theorem isStructField_elim_law_holds : isStructField_elim.law (GF := GF) := fun sf f => by
  unfold isStructField; exact .rfl

/-! ## Opening a schema's and a map type's lazy index (for `FindNamedType`, `Map.FindField`) -/

/-- An atomic pointer, given up for good (the lazy index once built). -/
theorem LawProofs.ownPointer_persist {T' : Type} [ZeroVal T'] [TypedPointsto (GF := GF) T']
    (u : Loc) (dq : DFrac) (v : Loc) :
    sync.atomic.ownPointer (GF := GF) (T' := T') u dq v ⊢
      |==> sync.atomic.ownPointer (T' := T') u DFrac.discard v := by
  rw [sync.atomic.ownPointer_unseal]; unfold sync.atomic.ownPointerDef
  exact (typedPointsto_dfractional _ _).dfractional_persist dq

instance LawProofs.ownPointer_discard_pers {T' : Type} [ZeroVal T'] [TypedPointsto (GF := GF) T']
    (u : Loc) (v : Loc) :
    Persistent (sync.atomic.ownPointer (GF := GF) (T' := T') u DFrac.discard v) := by
  rw [sync.atomic.ownPointer_unseal]; unfold sync.atomic.ownPointerDef; infer_instance

/-- A zero atomic pointer is an owned nil pointer. -/
theorem LawProofs.ownPointer_zero {T' : Type} [ZeroVal T'] [TypedPointsto (GF := GF) T'] (u : Loc) :
    u ↦ (zero_val (sync.atomic.Pointer T')) ⊢
      sync.atomic.ownPointer (GF := GF) (T' := T') u (DFrac.own 1) null := by
  rw [sync.atomic.ownPointer_unseal]; unfold sync.atomic.ownPointerDef
  exact .rfl

theorem LawProofs.isTypeDefs_lookup (n : GoString) : ∀ (tds : List schema.TypeDef)
    (ts : List (GoString × Atom)), (ts.map (·.1)).Nodup →
    isTypeDefs (GF := GF) false tds ts ⊢
      match lookupKV n ts with
      | some A => ∃ td, ⌜lastNamed (·.Name') n tds = some td ∧ td.Name' = n⌝ ∗
          isAtomOpt td.Atom' (some A)
      | none => ⌜lastNamed (·.Name') n tds = none⌝
  | [], [], _ => by
      simp only [lookupKV]; iintro _; ipureintro; exact LawProofs.lastNamed_nil _ _
  | [], _ :: _, _ => by unfold isTypeDefs; iintro %h; exact h.elim
  | _ :: _, [], _ => by unfold isTypeDefs; iintro %h; exact h.elim
  | td :: tds, (k, a) :: rest, hnd => by
      simp only [List.map_cons, List.nodup_cons] at hnd
      have ih := LawProofs.isTypeDefs_lookup n tds rest hnd.2
      rw [isTypeDefs.eq_2]
      iintro ⟨%hk, #Ha, Hr⟩
      rw [LawProofs.lastNamed_cons]
      unfold lookupKV
      by_cases hkn : k = n
      · subst hkn
        have hnone := LawProofs.lookupKV_none_of_not_mem (n := k) hnd.1
        rw [hnone] at ih
        ihave %hl := ih $$ Hr
        simp only [hl, hk, ite_true, Option.none_or]
        iexists td
        isplitr
        · ipureintro; exact ⟨rfl, hk⟩
        · unfold isAtomOpt; iexact Ha
      · have hkn' : td.Name' ≠ n := by rw [hk]; exact hkn
        simp only [hkn, hkn', ite_false, Option.or_none]
        iapply ih
        iexact Hr

theorem LawProofs.isFields_lookup (n : GoString) : ∀ (sfs : List schema.StructField)
    (fs : List (GoString × TypeRef)), (fs.map (·.1)).Nodup →
    isFields (GF := GF) sfs fs ⊢
      match lookupKV n fs with
      | some t => ∃ sf, ⌜lastNamed (·.Name') n sfs = some sf⌝ ∗ isStructField sf (n, t)
      | none => ⌜lastNamed (·.Name') n sfs = none⌝
  | [], [], _ => by
      simp only [lookupKV]; iintro _; ipureintro; exact LawProofs.lastNamed_nil _ _
  | [], _ :: _, _ => by unfold isFields; iintro %h; exact h.elim
  | _ :: _, [], _ => by unfold isFields; iintro %h; exact h.elim
  | sf :: sfs, (k, t) :: rest, hnd => by
      simp only [List.map_cons, List.nodup_cons] at hnd
      have ih := LawProofs.isFields_lookup n sfs rest hnd.2
      rw [isFields.eq_2]
      iintro ⟨#Hf, Hr⟩
      ihave #Hf2 := Hf
      iunfold isStructField at Hf2
      icases Hf2 with ⟨%hk0, -⟩
      have hk : sf.Name' = k := hk0.1
      rw [LawProofs.lastNamed_cons]
      unfold lookupKV
      by_cases hkn : k = n
      · subst hkn
        have hnone := LawProofs.lookupKV_none_of_not_mem (n := k) hnd.1
        rw [hnone] at ih
        ihave %hl := ih $$ Hr
        simp only [hl, hk, ite_true, Option.none_or]
        iexists sf
        isplitr
        · ipureintro; rfl
        · iexact Hf
      · have hkn' : sf.Name' ≠ n := by rw [hk]; exact hkn
        simp only [hkn, hkn', ite_false, Option.or_none]
        iapply ih
        iexact Hr

/-- **A shared schema, opened**: its type definitions and the once guarding its name index. -/
theorem LawProofs.isSchema_open (sc : Loc) (S : Schema) :
    isSchema (GF := GF) sc S ⊢
      ∃ (tys : GoSlice) (tds : List schema.TypeDef),
        sc.[schema.Schema, go!"Types"] ↦□ tys ∗ tys ↦*{DFrac.discard} tds ∗
        (□ ∀ n, ⌜(S.types.map (·.1)).Nodup⌝ -∗
          match S.find n with
          | some A => ∃ td, ⌜lastNamed (·.Name') n tds = some td ∧ td.Name' = n⌝ ∗
              isAtomOpt td.Atom' (some A)
          | none => ⌜lastNamed (·.Name') n tds = none⌝) ∗
        sync.isOnce sc.[schema.Schema, go!"once"]
          iprop(sc.[schema.Schema, go!"m"] ↦ (zero_val (sync.atomic.Pointer GoMap)))
          iprop(∃ (mp mm : Loc) (M : GMap GoString schema.TypeDef),
            sync.atomic.ownPointer (T' := GoMap) sc.[schema.Schema, go!"m"] DFrac.discard mp ∗
            mp ↦□ mm ∗ mm ↦$□ M ∗ ⌜∀ n, M !! n = lastNamed (·.Name') n tds⌝) := by
  unfold isSchema schemaRep lazyIndex Schema.find
  simp only [Bool.false_eq_true, ite_false]
  iintro ⟨%tys, %tds, #Ht, #Hs, #Hd, #Ho⟩
  iexists tys, tds
  iframe #
  imodintro
  iintro %n %hnd
  iapply LawProofs.isTypeDefs_lookup n tds S.types hnd
  iexact Hd

/-- **A map type, opened**: its fields and the once guarding its field index. -/
theorem LawProofs.isMapRep_open (m : Loc) (fs : List (GoString × TypeRef)) (e : Option TypeRef)
    (rel : ElemRel) :
    isMapRep (GF := GF) m fs e rel ⊢
      ∃ (fsl : GoSlice) (sfs : List schema.StructField),
        m.[schema.Map, go!"Fields"] ↦□ fsl ∗ fsl ↦*{DFrac.discard} sfs ∗
        (□ ∀ n, ⌜(fs.map (·.1)).Nodup⌝ -∗
          match lookupKV n fs with
          | some t => ∃ sf, ⌜lastNamed (·.Name') n sfs = some sf⌝ ∗ isStructField sf (n, t)
          | none => ⌜lastNamed (·.Name') n sfs = none⌝) ∗
        sync.isOnce m.[schema.Map, go!"once"]
          iprop(m.[schema.Map, go!"m"] ↦ (zero_val (sync.atomic.Pointer GoMap)))
          iprop(∃ (mp mm : Loc) (M : GMap GoString schema.StructField),
            sync.atomic.ownPointer (T' := GoMap) m.[schema.Map, go!"m"] DFrac.discard mp ∗
            mp ↦□ mm ∗ mm ↦$□ M ∗ ⌜∀ n, M !! n = lastNamed (·.Name') n sfs⌝) := by
  unfold isMapRep mapRep lazyIndex
  simp only [Bool.false_eq_true, ite_false]
  iintro ⟨%_, %fsl, %sfs, %us, %etv, #Hf, #Hs, #Hd, -, -, -, -, -, #Ho⟩
  iexists fsl, sfs
  iframe #
  imodintro
  iintro %n %hnd
  iapply LawProofs.isFields_lookup n sfs fs hnd
  iexact Hd

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

/-
**Helpers of `keyedAssociativeListItemToPathElement`'s proof** (part A3): the key field list it
builds, sorted by `FieldList.Sort` (a `mergeSort` by name), is `keyOf`'s `flSort` (both sort the
same fields by distinct names); a key `PathElement` built from it (`isPE_key_intro`).

Prove phase, round 2 (2026-11-20, notes/smd-plan.md).
-/
module

public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.LawProofsB2
public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.LawProofsA
public import Proof.sigs_k8s_io.structured_merge_diff.v7.value.LawProofsSort
public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.LawProofsA2
import all Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Defs

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace smd

open Iris Iris.BI Iris.ProgramLogic Iris.ProofMode
open sigs_k8s_io.structured_merge_diff.v7

namespace LawA3

/-! ## Sorting by distinct names -/

/-- Strictly sorted lists (by a strict order on a key) that are permutations of each other are
equal. -/
theorem eq_of_perm_strict {β : Type} (name : β → GoString) :
    ∀ (l1 l2 : List β), l1.Perm l2 →
      l1.Pairwise (fun a b => gsLt (name a) (name b) = true) →
      l2.Pairwise (fun a b => gsLt (name a) (name b) = true) → l1 = l2
  | [], l2, hp, _, _ => List.Perm.nil_eq hp
  | a :: xs, [], hp, _, _ => absurd hp.length_eq (by simp)
  | a :: xs, b :: ys, hp, h1, h2 => by
    rw [List.pairwise_cons] at h1 h2
    have hab : a = b := by
      refine Classical.byContradiction fun hne => ?_
      have ha : a ∈ ys := by
        have := hp.mem_iff.1 (List.mem_cons_self)
        rcases List.mem_cons.1 this with h | h
        · exact absurd h hne
        · exact h
      have hb : b ∈ xs := by
        have := hp.mem_iff.2 (List.mem_cons_self)
        rcases List.mem_cons.1 this with h | h
        · exact absurd h.symm hne
        · exact h
      have x1 := h1.1 b hb
      have x2 := h2.1 a ha
      have := ValuePure.gsLt_trans x1 x2
      rw [ValuePure.gsLt_irrefl] at this; cases this
    subst hab
    rw [eq_of_perm_strict name xs ys (List.Perm.cons_inv hp) h1.2 h2.2]

theorem flInsert_sorted (f : GoString × UVal) :
    ∀ l : FieldList, l.Pairwise (fun a b => gsLt a.1 b.1 = true) → f.1 ∉ l.map (·.1) →
      (flInsert f l).Pairwise (fun a b => gsLt a.1 b.1 = true)
  | [], _, _ => by simp [flInsert]
  | g :: gs, hs, hn => by
    unfold flInsert
    rw [List.pairwise_cons] at hs
    simp only [List.map_cons, List.mem_cons, not_or] at hn
    split
    · rename_i hlt
      refine List.pairwise_cons.2 ⟨?_, List.pairwise_cons.2 hs⟩
      intro c hc
      rcases List.mem_cons.1 hc with rfl | hc
      · exact hlt
      · exact ValuePure.gsLt_trans hlt (hs.1 c hc)
    · rename_i hlt
      have hgf : gsLt g.1 f.1 = true := by
        rcases ValuePure.gsLt_false_cases (Bool.eq_false_iff.2 hlt) with h | h
        · exact h
        · exact absurd h hn.1
      refine List.pairwise_cons.2 ⟨?_, flInsert_sorted f gs hs.2 hn.2⟩
      intro c hc
      have := (LawB.flInsert_perm f gs).mem_iff.1 hc
      rcases List.mem_cons.1 this with rfl | hc
      · exact hgf
      · exact hs.1 c hc

theorem foldl_flInsert_sorted : ∀ (fl acc : FieldList),
    acc.Pairwise (fun a b => gsLt a.1 b.1 = true) → ((fl ++ acc).map (·.1)).Nodup →
      (fl.foldl (fun acc f => flInsert f acc) acc).Pairwise (fun a b => gsLt a.1 b.1 = true)
  | [], acc, h, _ => h
  | f :: fl, acc, h, hn => by
    simp only [List.foldl_cons]
    simp only [List.cons_append, List.map_cons, List.nodup_cons, List.map_append,
      List.mem_append, not_or] at hn
    apply foldl_flInsert_sorted fl _ (flInsert_sorted f acc h hn.1.2)
    have hp : ((fl ++ flInsert f acc).map (·.1)).Perm ((fl ++ f :: acc).map (·.1)) :=
      ((List.Perm.append_left fl (LawB.flInsert_perm f acc))).map _
    refine hp.nodup_iff.2 ?_
    have : ((fl ++ f :: acc).map (·.1)).Perm ((f :: (fl ++ acc)).map (·.1)) :=
      (List.perm_middle).map _
    refine this.nodup_iff.2 ?_
    simp only [List.map_cons, List.nodup_cons, List.map_append, List.mem_append, not_or]
    exact ⟨hn.1, hn.2⟩

theorem flSort_sorted (fl : FieldList) (hn : (fl.map (·.1)).Nodup) :
    (flSort fl).Pairwise (fun a b => gsLt a.1 b.1 = true) :=
  foldl_flInsert_sorted fl [] List.Pairwise.nil (by simpa using hn)

theorem zip_names {α β γ : Type} (f : α → γ) (g : β → γ) :
    ∀ (l1 : List α) (l2 : List β), l1.map f = l2.map g → ∀ p ∈ l1.zip l2, f p.1 = g p.2
  | [], _, _, p, hp => by simp at hp
  | _ :: _, [], _, p, hp => by simp at hp
  | a :: l1, b :: l2, h, p, hp => by
    simp only [List.map_cons, List.cons.injEq] at h
    simp only [List.zip_cons_cons, List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact h.1
    · exact zip_names f g l1 l2 h.2 p hp

/-- The names of an item's key fields, in key order, are among the key names. -/
theorem keyNames_sublist (ks : List GoString) (kvs : List (GoString × UVal)) :
    ((ks.filterMap (fun k => (lookupKV k kvs).map (fun v => (k, v)))).map (·.1)).Sublist ks := by
  induction ks with
  | nil => simp
  | cons k ks ih =>
    rw [List.filterMap_cons]
    cases lookupKV k kvs with
    | none => exact ih.cons k
    | some v => exact ih.cons₂ k

/-! ## A list's field sets, item by item -/

theorem mem_pu (a b : PathSet) (q : Path) : q ∈ PathSet.union a b ↔ q ∈ a ∨ q ∈ b :=
  FSet.mem_union' a b q

theorem mem_fieldsL_append (S : Schema) (e : TypeRef) (ks : List GoString) (p : Path) (q : Path) :
    ∀ (l1 l2 : List UVal),
      q ∈ fieldsL S e ks p (l1 ++ l2) ↔ q ∈ fieldsL S e ks p l1 ∨ q ∈ fieldsL S e ks p l2
  | [], l2 => by simp only [List.nil_append, fieldsL]; exact ⟨Or.inr, fun h => h.elim (fun h => absurd h (FSet.mem_empty _)) id⟩
  | a :: l1, l2 => by
    simp only [List.cons_append, fieldsL]
    cases keyOf ks a with
    | none => exact mem_fieldsL_append S e ks p q l1 l2
    | some pe =>
      simp only [union, mem_pu, mem_fieldsL_append S e ks p q l1 l2, or_assoc]

/-- The field set of the first `j + 1` items: the first `j`'s, then the item's fields and the
item's path. -/
theorem fieldsL_step (F : PathSet) (S : Schema) (e : TypeRef) (ks : List GoString) (p : Path)
    (vs : List UVal) (j : Nat) (x : UVal) (pe : PE) (hx : vs[j]? = some x)
    (hk : keyOf ks x = some pe) :
    PathSet.union (PathSet.union (PathSet.union F (fieldsL S e ks p (vs.take j)))
      (fieldsAt S e (p ++ [pe]) x)) (PathSet.single (p ++ [pe])) =
      PathSet.union F (fieldsL S e ks p (vs.take (j + 1))) := by
  apply FSet.ext'
  intro q
  rw [List.take_add_one, hx]
  simp only [Option.toList_some, mem_pu, mem_fieldsL_append]
  simp only [fieldsL, hk, union, mem_pu]
  have he : q ∉ (empty : PathSet) := FSet.mem_empty q
  simp only [or_assoc, he, or_false, ins]

theorem fieldsL_take_sub (S : Schema) (e : TypeRef) (ks : List GoString) (p : Path)
    (vs : List UVal) (j : Nat) (q : Path) (h : q ∈ fieldsL S e ks p (vs.take j)) :
    q ∈ fieldsL S e ks p vs := by
  rw [← List.take_append_drop j vs, mem_fieldsL_append]; exact Or.inl h

theorem cardLt_sub (A B : PathSet) (n : Nat) (h : ∀ q, q ∈ A → q ∈ B) (hB : B.CardLt n) :
    A.CardLt n :=
  Nat.lt_of_le_of_lt (FSet.card_le_of_subset _ _ h) hB

end LawA3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

namespace LawA3

/-- `FieldList.Sort`'s order on fields, on the pairs. -/
def fieldLe (a b : value.Field × (GoString × UVal)) : Bool := !gsLt b.1.Name' a.1.Name'

/-- `FieldList.Sort`'s `mergeSort` of fields paired with a `FieldList` of the same names: the
sorted pairs `P'` give both the sorted fields and `flSort`. -/
theorem sort_pairs (P : List (value.Field × (GoString × UVal)))
    (hname : ∀ p ∈ P, p.1.Name' = p.2.1) (hnd : (P.map (·.2.1)).Nodup) :
    ∃ P' : List (value.Field × (GoString × UVal)), P'.Perm P ∧
      (P.map (·.1)).mergeSort (fun a b => !gsLt b.Name' a.Name') = P'.map (·.1) ∧
      flSort (P.map (·.2)) = P'.map (·.2) := by
  let le := fieldLe
  refine ⟨P.mergeSort le, List.mergeSort_perm P le, ?_, ?_⟩
  · exact (List.map_mergeSort (f := fun p : value.Field × (GoString × UVal) => p.1)
      (s := fun a b : value.Field => !gsLt b.Name' a.Name') (fun a _ b _ => rfl)).symm
  · have hperm : ((P.mergeSort le).map (·.2)).Perm (P.map (·.2)) :=
      (List.mergeSort_perm P le).map _
    apply eq_of_perm_strict (fun f => f.1)
    · exact (LawB.flSort_perm _).trans hperm.symm
    · exact flSort_sorted _ (by rw [List.map_map]; exact hnd)
    · have hs : (P.mergeSort le).Pairwise (fun a b => le a b = true) := List.pairwise_mergeSort (le := le)
        (fun a b c h1 h2 => by
          simp only [le, fieldLe, Bool.not_eq_true'] at h1 h2 ⊢
          exact ValuePure.gsLt_false_trans h1 h2)
        (fun a b => by
          simp only [le, fieldLe]
          cases h : gsLt b.1.Name' a.1.Name'
          · rfl
          · have : gsLt a.1.Name' b.1.Name' = false := by
              cases h' : gsLt a.1.Name' b.1.Name'
              · rfl
              · have := ValuePure.gsLt_trans h h'; rw [ValuePure.gsLt_irrefl] at this; cases this
            simp [this]) P
      have hnd' : ((P.mergeSort le).map (·.2.1)).Nodup :=
        ((List.mergeSort_perm P le).map _).nodup_iff.2 hnd
      rw [List.pairwise_map]
      rw [List.nodup_iff_pairwise_ne, List.pairwise_map] at hnd'
      have hmem : ∀ p ∈ P.mergeSort le, p.1.Name' = p.2.1 :=
        fun p hp => hname p ((List.mergeSort_perm P le).mem_iff.1 hp)
      refine (List.Pairwise.and hs hnd').imp_of_mem ?_
      intro a b ha hb ⟨h1, h2⟩
      simp only [le, fieldLe, Bool.not_eq_true'] at h1
      rw [hmem a ha, hmem b hb] at h1
      rcases ValuePure.gsLt_false_cases h1 with h | h
      · exact h
      · exact absurd h.symm h2

theorem zip_map_fst_snd {α β : Type} : ∀ (P : List (α × β)), (P.map (·.1)).zip (P.map (·.2)) = P
  | [] => rfl
  | p :: P => by simp only [List.map_cons, List.zip_cons_cons, zip_map_fst_snd P]

/-- A list's persistent members, from a persistent universal. -/
theorem sepL_of_forall {α : Type} (f : α → IProp GF) :
    ∀ (L : List α), (□ ∀ a, ⌜a ∈ L⌝ -∗ f a) ⊢ sepL f L
  | [] => by iintro -; rw [LawProofs.sepL_nil]; ipureintro; trivial
  | a :: L => by
    iintro #H
    rw [LawProofs.sepL_cons]
    isplitl
    · iapply H; ipureintro; exact List.mem_cons_self
    · iapply sepL_of_forall f L
      imodintro
      iintro %b %hb
      iapply H; ipureintro; exact List.mem_cons_of_mem _ hb

/-- A wrapper's interface is a `*valueUnstructured` (kept). -/
theorem isValF_shape (v : value.Value) (dq : DFrac) (x : UVal) :
    isValF (GF := GF) v dq x ⊢ isValF v dq x ∗
      ⌜∃ p : Loc, v = interface.mkOk (go.GoType.PointerType value.valueUnstructured.ty) #p⌝ :=
  pure_elim (∃ p : Loc, v = interface.mkOk (go.GoType.PointerType value.valueUnstructured.ty) #p)
    ((isValF_concrete_law_holds v dq x).trans (by
    iintro ⟨%p, %h⟩; ipureintro; exact ⟨p, h⟩)) (fun h => by
      iintro H; iframe; ipureintro; exact h)

/-- A key field's value (a declared scalar field of a conforming map) has no maps inside. -/
theorem keyVal_mapLensOk (S : Schema) (t : TypeRef) (v : UVal) (s : Scalar)
    (hf : S.find t.name = some (.scalar s)) (hc : conforms S t v) : v.mapLensOk = true := by
  cases v <;> simp_all [conforms, conformsB, UVal.mapLensOk]

/-- A key `PathElement` (`PathElement{Key: &keyMap}`). -/
theorem isPE_key_intro (e : fieldpath.PathElement) (s : GoSlice) (fl : FieldList)
    (hn : e.FieldName' = null) (hl : fl.all (fun f => f.2.mapLensOk) = true) :
    e.Key' ↦□ s ∗ isFieldList s fl ⊢ isPE (GF := GF) e (.key fl) := by
  unfold isPE
  iintro ⟨#Hk, #Hf⟩
  isplitr
  · ipureintro; exact ⟨hn, hl⟩
  iexists s
  iframe #

/-- A list view's `Length` and `At` (`isListV_dispatchA` without `AtUsing`). -/
theorem isListV_dispatchL [package_sem : typed.Assumptions]
    (hL : value.listUnstructured.Length.spec (GF := GF))
    (hLP : value.listUnstructured.Length_ptr.spec (GF := GF))
    (hT : value.listUnstructured.At.spec (GF := GF))
    (hTP : value.listUnstructured.At_ptr.spec (GF := GF))
    (l : value.List') (vs : List UVal) :
    isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.value ∗ isListV l vs ⊢
      ∃ i, ⌜l = .ok i⌝ ∗
        □ ({{ True }} (App (Val #(methods i.ty go!"Length" i.v)) (Val #()))
            {{ (r : w64), RET #r; ⌜r.toInt = vs.length⌝ }}) ∗
        □ (∀ (n : w64) (x : UVal),
            {{ ⌜0 ≤ n.toInt ∧ vs[n.toInt.toNat]? = some x⌝ }}
            (App (Val #(methods i.ty go!"At" i.v)) (Val #n))
            {{ (v : value.Value), RET #v; isValF v (DFrac.own 1) x }}) := by
  iintro ⟨#Hpkg, Hl⟩
  ihave #Hl := isListV_persistent_law_holds l vs $$ Hl
  ihave %Hc := isListV_concrete_law_holds l vs $$ Hl
  rcases Hc with ⟨sl, rfl⟩ | ⟨p, rfl⟩
  · iexists _
    isplitr
    · ipureintro; rfl
    isplitr
    · imodintro
      iintro %Φ !> - HΦ
      iapply hL sl vs $$ [] [HΦ]
      · iframe #
      · iexact HΦ
    · imodintro
      iintro %n %x %Φ !> %h HΦ
      iapply hT sl vs n x $$ [] [HΦ]
      · iframe #; ipureintro; exact h
      · iexact HΦ
  · iexists _
    isplitr
    · ipureintro; rfl
    isplitr
    · imodintro
      iintro %Φ !> - HΦ
      iapply hLP p vs $$ [] [HΦ]
      · iframe #
      · iexact HΦ
    · imodintro
      iintro %n %x %Φ !> %h HΦ
      iapply hTP p vs n x $$ [] [HΦ]
      · iframe #; ipureintro; exact h
      · iexact HΦ

end LawA3

end proof

end smd
end EtcdGrove
end Perennial

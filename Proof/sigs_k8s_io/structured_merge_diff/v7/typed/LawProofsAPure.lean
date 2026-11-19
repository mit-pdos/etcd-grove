/-
**Proofs of `typed`'s pure laws about validation, field sets and removal** (`WalkerLaws.lean`),
part A: `fieldSet_fieldsAt`, `fieldSet_card`, `removeAt_scalar`, `conforms_item`,
`conforms_entry`.

Prove phase (2026-11-19, notes/smd-plan.md).
-/
module

public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.WalkerLaws
public import Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.LawProofs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace smd

open sigs_k8s_io.structured_merge_diff.v7

namespace LawA

theorem fieldSet_fieldsAt_law_holds : fieldSet_fieldsAt.law := fun _ _ _ => rfl

theorem removeAt_scalar_law_holds : removeAt_scalar.law := by
  intro S t s R x h
  cases x <;> simp [removeAt, h]

/-! ## Conformance of the children -/

theorem conformsL_iff (S : Schema) (e : TypeRef) (vs : List UVal) :
    conformsL S e vs = true ↔ ∀ v ∈ vs, conforms S e v := by
  induction vs with
  | nil => simp [conformsL]
  | cons v vs ih => simp [conformsL, ih, conforms]

theorem conformsM_mem (S : Schema) (fs : List (GoString × TypeRef)) (e : Option TypeRef)
    (kvs : List (GoString × UVal)) (h : conformsM S fs e kvs = true) :
    ∀ k v, (k, v) ∈ kvs → ∃ t', fieldType fs e k = some t' ∧ conforms S t' v := by
  induction kvs with
  | nil => intro k v hm; simp at hm
  | cons kv kvs ih =>
    obtain ⟨k0, v0⟩ := kv
    simp only [conformsM, Bool.and_eq_true] at h
    obtain ⟨h0, hr⟩ := h
    intro k v hm
    rcases List.mem_cons.1 hm with heq | hm
    · cases heq
      split at h0
      · next t' ht => exact ⟨t', ht, h0⟩
      · simp at h0
    · exact ih hr k v hm

theorem conforms_item_law_holds : conforms_item.law := by
  intro S t e rel ks vs hf hc
  unfold conforms at hc
  simp only [conformsB, hf, Bool.and_eq_true] at hc
  obtain ⟨hl, ha⟩ := hc
  refine ⟨(conformsL_iff S e vs).1 hl, fun hrel => ?_⟩
  subst hrel
  simp only [ite_true, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at ha
  exact ⟨fun v hv => ha.1 v hv, ha.2⟩

theorem conforms_entry_law_holds : conforms_entry.law := by
  intro S t fs e rel kvs hf hc
  unfold conforms at hc
  simp only [conformsB, hf] at hc
  exact conformsM_mem S fs e kvs hc

/-! ## The size of a field set -/

theorem card_empty : (empty : PathSet).card = 0 := rfl

theorem card_ins (p : Path) : (ins p).card ≤ 1 := by
  show (FSet.dedupL ([p].filter (fun p => !p.isEmpty))).length ≤ 1
  cases p <;> simp [FSet.dedupL]

theorem card_union (a b : PathSet) : (union a b).card ≤ a.card + b.card :=
  FSet_card_union_law_holds a b

mutual
theorem fieldsAt_card (S : Schema) (t : TypeRef) (p : Path) :
    ∀ x : UVal, (fieldsAt S t p x).card + 1 ≤ 2 * x.size
  | .list vs => by
    have := fieldsL_card_all S p vs
    rw [fieldsAt, UVal.size]
    split
    · have := card_ins p; omega
    · exact Nat.le_trans (Nat.add_le_add_right (this _ _) 1) (by omega)
    · rw [card_empty]; omega
  | .map kvs => by
    have := fieldsM_card_all S p kvs
    rw [fieldsAt, UVal.size]
    split
    · have := card_ins p; omega
    · exact Nat.le_trans (Nat.add_le_add_right (this _ _) 1) (by omega)
    · rw [card_empty]; omega
  | .null => by
    unfold fieldsAt; simp only [UVal.size]
    split <;> first | (have := card_ins p; omega) | (rw [card_empty]; omega)
  | .bool _ => by
    unfold fieldsAt; simp only [UVal.size]
    split <;> first | (have := card_ins p; omega) | (rw [card_empty]; omega)
  | .int _ => by
    unfold fieldsAt; simp only [UVal.size]
    split <;> first | (have := card_ins p; omega) | (rw [card_empty]; omega)
  | .str _ => by
    unfold fieldsAt; simp only [UVal.size]
    split <;> first | (have := card_ins p; omega) | (rw [card_empty]; omega)
theorem fieldsL_card_all (S : Schema) (p : Path) :
    ∀ vs : List UVal, ∀ (e : TypeRef) (ks : List GoString),
      (fieldsL S e ks p vs).card ≤ 2 * UVal.sizeL vs
  | [] => fun e ks => by rw [fieldsL, card_empty]; omega
  | v :: vs => fun e ks => by
    have ih := fieldsL_card_all S p vs e ks
    rw [fieldsL, UVal.sizeL]
    split
    · next pe _ =>
      have h1 := fieldsAt_card S e (p ++ [pe]) v
      have h2 := card_union (union (fieldsAt S e (p ++ [pe]) v) (ins (p ++ [pe])))
        (fieldsL S e ks p vs)
      have h3 := card_union (fieldsAt S e (p ++ [pe]) v) (ins (p ++ [pe]))
      have h4 := card_ins (p ++ [pe])
      omega
    · have h1 := fieldsAt_card S e p v
      omega
theorem fieldsM_card_all (S : Schema) (p : Path) :
    ∀ kvs : List (GoString × UVal), ∀ (fs : List (GoString × TypeRef)) (e : Option TypeRef),
      (fieldsM S fs e p kvs).card ≤ 2 * UVal.sizeM kvs
  | [] => fun fs e => by rw [fieldsM, card_empty]; omega
  | (k, v) :: kvs => fun fs e => by
    have ih := fieldsM_card_all S p kvs fs e
    rw [fieldsM, UVal.sizeM]
    split
    · next t _ =>
      have hu := card_union (union (fieldsAt S t (p ++ [.field k]) v)
          (if v = .null ∨ v = .map [] ∨ lookupKV k fs = none then ins (p ++ [.field k]) else empty))
        (fieldsM S fs e p kvs)
      have h1 := fieldsAt_card S t (p ++ [.field k]) v
      have h3 := card_union (fieldsAt S t (p ++ [.field k]) v)
        (if v = .null ∨ v = .map [] ∨ lookupKV k fs = none then ins (p ++ [.field k]) else empty)
      have h4 : (if v = .null ∨ v = .map [] ∨ lookupKV k fs = none then ins (p ++ [.field k])
          else empty).card ≤ 1 := by
        split
        · exact card_ins _
        · rw [card_empty]; omega
      omega
    · have hu := card_union empty (fieldsM S fs e p kvs)
      rw [card_empty] at hu
      omega
end

theorem fieldSet_card_law_holds : fieldSet_card.law := by
  intro S t p x hx
  have := fieldsAt_card S t p x
  unfold FSet.CardLt
  simp only [smdSizeMax] at hx
  omega

end LawA

export LawA (fieldSet_fieldsAt_law_holds removeAt_scalar_law_holds conforms_item_law_holds
  conforms_entry_law_holds fieldSet_card_law_holds)

end smd
end EtcdGrove
end Perennial

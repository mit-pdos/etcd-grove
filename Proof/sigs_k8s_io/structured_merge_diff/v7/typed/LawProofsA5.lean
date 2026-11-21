/-
**Helpers of the removing walker's `doMap` body** (part A5): `removeAt` of a map type unfolded
case by case; `removeM` as the per-key results over the entries' keys (`LawBMZ.entriesOf`), what
a Go map filled in any order holds.

Prove phase, round 2 (2026-11-20, notes/smd-plan.md).
-/
module

public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.LawProofsA4
public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.LawProofsBMapZip

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace smd

open Iris Iris.BI Iris.ProgramLogic Iris.ProofMode
open sigs_k8s_io.structured_merge_diff.v7

namespace LawA5

/-- A map type's `removeAt` of a value not a map: `null`. -/
theorem removeAt_map_nonmap (S : Schema) (t : TypeRef) (fs : List (GoString × TypeRef))
    (e : Option TypeRef) (rel : ElemRel) (R : PathSet) (x : UVal)
    (h : S.find t.name = some (.map fs e rel)) (hx : x.isMapB = false) :
    removeAt S t R x = .null := by
  cases x <;> simp_all [removeAt, UVal.isMapB]

/-- A map type's `removeAt` of an empty map or an atomic one: `null`. -/
theorem removeAt_map_leaf (S : Schema) (t : TypeRef) (fs : List (GoString × TypeRef))
    (e : Option TypeRef) (rel : ElemRel) (R : PathSet) (kvs : List (GoString × UVal))
    (h : S.find t.name = some (.map fs e rel)) (hl : kvs = [] ∨ rel = .atomic) :
    removeAt S t R (.map kvs) = .null := by
  rw [removeAt, h]
  rcases hl with rfl | rfl <;> simp

/-- A map type's `removeAt` of a granular non-empty map: its entries' `removeM` (`null` if none
are left). -/
theorem removeAt_map_items (S : Schema) (t : TypeRef) (fs : List (GoString × TypeRef))
    (e : Option TypeRef) (rel : ElemRel) (R : PathSet) (kvs : List (GoString × UVal))
    (h : S.find t.name = some (.map fs e rel)) (hne : kvs ≠ []) (hr : rel ≠ .atomic) :
    removeAt S t R (.map kvs) =
      if removeM S fs e R kvs = [] then .null else .map (removeM S fs e R kvs) := by
  rw [removeAt, h]
  have : ¬ (kvs.isEmpty = true ∨ rel = .atomic) := by
    rintro (h1 | h1)
    · exact hne (List.isEmpty_iff.1 h1)
    · exact hr h1
  simp only [this, ite_false]
  cases removeM S fs e R kvs <;> simp

/-- The entry key `k` of value `v` becomes (`removeM`'s step): `none` if removed. -/
def rmEntry (S : Schema) (fs : List (GoString × TypeRef)) (e : Option TypeRef) (R : PathSet)
    (k : GoString) (v : UVal) : Option UVal :=
  if [.field k] ∈ R then none
  else if ¬ (R.under (.field k)).IsEmpty then
    some (match fieldType fs e k with
      | some t => removeAt S t (R.under (.field k)) v
      | none => .null)
  else some v

/-- The entry of key `k` after the removal, from the map's entries `kvs`. -/
def gRm (S : Schema) (fs : List (GoString × TypeRef)) (e : Option TypeRef) (R : PathSet)
    (kvs : List (GoString × UVal)) (k : GoString) : Option UVal :=
  (lookupKV k kvs).bind (rmEntry S fs e R k)

theorem entriesOf_congr (f g : GoString → Option UVal) :
    ∀ ks : List GoString, (∀ k ∈ ks, f k = g k) → LawBMZ.entriesOf f ks = LawBMZ.entriesOf g ks
  | [], _ => rfl
  | k :: ks, h => by
    unfold LawBMZ.entriesOf at *
    rw [List.filterMap_cons, List.filterMap_cons, h k List.mem_cons_self]
    have := entriesOf_congr f g ks (fun k' hk' => h k' (List.mem_cons_of_mem _ hk'))
    unfold LawBMZ.entriesOf at this
    rw [this]

/-- **`removeM` is the per-key results over the entries' keys.** -/
theorem removeM_entriesOf (S : Schema) (fs : List (GoString × TypeRef)) (e : Option TypeRef)
    (R : PathSet) : ∀ kvs : List (GoString × UVal), (kvs.map (·.1)).Nodup →
      removeM S fs e R kvs = LawBMZ.entriesOf (gRm S fs e R kvs) (kvs.map (·.1))
  | [], _ => by simp [removeM, LawBMZ.entriesOf]
  | (k, v) :: kvs, hnd => by
    have hnd' : (kvs.map (·.1)).Nodup := (List.nodup_cons.1 hnd).2
    have hk : k ∉ kvs.map (·.1) := (List.nodup_cons.1 hnd).1
    have ih := removeM_entriesOf S fs e R kvs hnd'
    have hc : LawBMZ.entriesOf (gRm S fs e R ((k, v) :: kvs)) (kvs.map (·.1)) =
        LawBMZ.entriesOf (gRm S fs e R kvs) (kvs.map (·.1)) := by
      apply entriesOf_congr
      intro k' hk'
      have hne : k ≠ k' := fun h => hk (h ▸ hk')
      simp [gRm, lookupKV, hne]
    simp only [List.map_cons]
    unfold LawBMZ.entriesOf
    rw [List.filterMap_cons]
    unfold LawBMZ.entriesOf at hc ih
    rw [hc, ← ih]
    have hg : gRm S fs e R ((k, v) :: kvs) k = rmEntry S fs e R k v := by simp [gRm, lookupKV]
    rw [hg, removeM]
    unfold rmEntry
    by_cases h1 : [PE.field k] ∈ R
    · simp [h1]
    · by_cases h2 : (R.under (.field k)).IsEmpty <;> simp [h1, h2] <;>
        cases fieldType fs e k <;> rfl

/-- `lookupKV` of a list with one more entry at the end. -/
theorem lkv_snoc {α : Type} (n : GoString) (f : GoString × α) :
    ∀ l : List (GoString × α), lookupKV n (l ++ [f]) =
      match lookupKV n l with
      | some v => some v
      | none => if f.1 = n then some f.2 else none
  | [] => by simp [lookupKV]
  | (k', v') :: rest => by
    have ih := lkv_snoc n f rest
    by_cases h : k' = n <;> simp [lookupKV, h, ih]

theorem lkv_none_of_not_mem {α : Type} (n : GoString) :
    ∀ l : List (GoString × α), n ∉ l.map (·.1) → lookupKV n l = none
  | [], _ => rfl
  | (k', v') :: rest, h => by
    simp only [List.map_cons, List.mem_cons, not_or] at h
    have hk : k' ≠ n := fun e => h.1 e.symm
    simp [lookupKV, hk, lkv_none_of_not_mem n rest h.2]

/-- **A declared fields' prefix one longer** (names distinct): the new field's name maps to its
type, the others as before. -/
theorem lkv_take_succ {α : Type} (fs : List (GoString × α)) (j : Nat) (f : GoString × α)
    (hf : fs[j]? = some f) (hnd : (fs.map (·.1)).Nodup) (n : GoString) :
    lookupKV n (fs.take (j + 1)) = if f.1 = n then some f.2 else lookupKV n (fs.take j) := by
  have ht : fs.take (j + 1) = fs.take j ++ [f] := by
    rw [List.take_add_one, hf]; rfl
  have hnd2 : ((fs.take j ++ [f]).map (·.1)).Nodup := by
    rw [← ht, List.map_take]
    exact hnd.sublist (List.take_sublist _ _)
  rw [List.map_append, List.nodup_append] at hnd2
  have hnot : f.1 ∉ (fs.take j).map (·.1) := by
    intro hm
    exact hnd2.2.2 _ hm _ (by simp) rfl
  rw [ht, lkv_snoc]
  by_cases hn : f.1 = n
  · subst hn
    simp [lkv_none_of_not_mem _ _ hnot]
  · simp only [hn, ite_false]
    cases lookupKV n (fs.take j) <;> rfl

section wp
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **A range loop over a slice the loop only reads** (`for _, x := range s { body }`): `P i`
holds before the `i`-th iteration, and the body ends normally (a copy of
`Proof/k8s_io/api/DeepCopyBase.lean`'s, which this tier does not import). -/
theorem wp_slice_for_range {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] (t : go.GoType)
    [IntoValTyped (GF := GF) V t] (sl : GoSlice) (vs : List V) (dq : DFrac) (body : GoFunc)
    (P : Nat → IProp GF) (Φ : val → IProp GF) :
    sl ↦*{dq} vs -∗ P 0 -∗
    □ (∀ (i : Nat) (x : V), ⌜vs[i]? = some x⌝ -∗ P i -∗ sl ↦*{dq} vs -∗
        WP (App (App (Val #body) (Val #(W64 i))) (Val #x))
          {{ bv, ⌜bv = executeVal⌝ ∗ P (i + 1) ∗ sl ↦*{dq} vs }}) -∗
    (P vs.length -∗ sl ↦*{dq} vs -∗ Φ executeVal) -∗
    WP (App (App (Val (slice.forRange t)) (Val #sl)) (Val #body)) {{ Φ }} := by
  iintro Hs HP #Hiter HΦ
  ihave %Hlen := ownSlice_len _ _ _ $$ Hs
  wp_auto
  ihave Hinv : (∃ (j : Nat), "i" ∷ i_ptr ↦ W64 j ∗ "HP" ∷ P j ∗ "Hs" ∷ sl ↦*{dq} vs ∗
      "HΦ" ∷ (P vs.length -∗ sl ↦*{dq} vs -∗ Φ executeVal) ∗ "%Hj" ∷ ⌜j ≤ vs.length⌝ :
      IProp GF) $$ [i HP Hs HΦ]
  · iexists 0
    iframe
    ipureintro; omega
  wp_for Hinv
  by_cases hj : j < vs.length
  · have hc : sint.Z (W64 (j : Int)) < sint.Z sl.len := by word
    simp only [decide_eq_true hc, ↓reduceIte]
    wp_auto
    have h0 : 0 ≤ sint.Z (W64 (j : Int)) := by word
    simp only [h0, hc, and_self, ↓reduceIte]
    have hsj : (sint.Z (W64 (j : Int))).toNat = j := by word
    obtain ⟨x, hx⟩ : ∃ x, vs[j]? = some x := ⟨_, List.getElem?_eq_getElem hj⟩
    wp_apply (wp_load_slice_index (t := t) sl (sint.Z (W64 (j : Int))) vs dq x h0) $$ [Hs] as Hs
    · iframe; ipureintro; rw [hsj]; exact hx
    iapply wp_wand $$ (Hiter $$ %j %x %hx HP Hs)
    iintro %bv ⟨%hbv, HP, Hs⟩
    subst hbv
    iapply wp_for_post_do
    wp_auto
    iframe
    iexists (j + 1)
    have hw : W64 (j : Int) + W64 1 = W64 ((j + 1 : Nat) : Int) := by word
    rw [hw]
    have hj1 : j + 1 ≤ vs.length := hj
    iframe
    ipureintro; exact hj1
  · have hc : ¬ sint.Z (W64 (j : Int)) < sint.Z sl.len := by word
    simp only [decide_eq_false hc, Bool.false_eq_true, ↓reduceIte]
    have hjl : j = vs.length := by omega
    subst hjl
    iapply HΦ $$ HP Hs

end wp

end LawA5

end smd
end EtcdGrove
end Perennial

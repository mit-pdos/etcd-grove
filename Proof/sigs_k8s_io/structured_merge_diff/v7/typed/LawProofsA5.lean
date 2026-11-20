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

end LawA5

end smd
end EtcdGrove
end Perennial

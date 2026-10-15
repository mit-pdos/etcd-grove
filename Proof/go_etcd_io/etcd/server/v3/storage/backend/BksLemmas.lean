/-
Lemmas on a buckets map (`txBuffer.buckets`) and its buffers' big separating conjunction
(`[∗map] _id ↦ x;es ∈ P;B, bbAt x.1 dq x.2 es`, the second conjunct of `bksAt`): taking one buffer
out and putting it back, deleting and inserting one; the `buckets` field of a `txBuffer` at a
fraction; and the empty results (`kvsOut` of nothing). Lean-first (no Rocq counterpart); see
`InvBuffer.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvBuffer

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace backend

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.backend

/-! ## A map range's keys (`wp_map_for_range`: the `i`-th key, those before it) -/

/-- The `n`-th key is not among the first `n` (distinct keys). -/
theorem not_mem_take_of_getElem? {α} {l : List α} (hnd : l.Nodup) {n : Nat} {a : α}
    (h : l[n]? = some a) : a ∉ l.take n := by
  intro hm
  obtain ⟨j, hj, hja⟩ := List.mem_take_iff_getElem.1 hm
  have h1 : l[j]? = some a := by rw [List.getElem?_eq_getElem (by omega)]; exact congrArg some hja
  have := list_nodup_getElem?_inj l hnd j n a h1 h
  omega

/-- The first `n + 1` keys: the first `n` and the `n`-th. -/
theorem mem_take_succ_iff {α} {l : List α} {n : Nat} {a : α} (h : l[n]? = some a) (x : α) :
    x ∈ l.take (n + 1) ↔ x ∈ l.take n ∨ x = a := by
  rw [List.take_add_one, h]
  simp

/-- A map restricted to the first `n + 1` keys. -/
theorem gmap_filter_take_succ {V} (B : GMap w64 V) (keys : List w64) (n : Nat) (k : w64) (v : V)
    (hk : keys[n]? = some k) (hB : B !! k = some v) :
    B.filter (fun j _ => decide (j ∈ keys.take (n + 1))) =
      <[k := v]> (B.filter (fun j _ => decide (j ∈ keys.take n))) := by
  ext j
  simp only [GMap.lookup_filter, mem_take_succ_iff hk]
  by_cases hj : j = k
  · subst hj; rw [GMap.lookup_insert, hB]; simp
  · rw [GMap.lookup_insert_ne _ _ (Ne.symm hj)]; simp [hj]

/-- A map restricted to all its keys. -/
theorem gmap_filter_take_length {V} (B : GMap w64 V) (keys : List w64)
    (h : ∀ k, (B !! k).isSome → k ∈ keys) :
    B.filter (fun j _ => decide (j ∈ keys.take keys.length)) = B := by
  ext j
  simp only [GMap.lookup_filter, List.take_length]
  cases hb : B !! j with
  | none => rfl
  | some v => simp [h j (by rw [hb]; rfl)]

/-- A map restricted to no keys. -/
theorem gmap_filter_take_zero {V} (B : GMap w64 V) (keys : List w64) :
    B.filter (fun j _ => decide (j ∈ keys.take 0)) = ∅ := by
  ext j
  simp only [GMap.lookup_filter, List.take_zero]
  cases B !! j <;> rfl

section lemmas
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

/-! ## The `buckets` field of a `txBuffer` -/

/-- The `buckets` field of a `txBuffer` at any fraction (the struct-level load accessor does not
fire at a general fraction), and the struct back. -/
theorem txBuffer_buckets_acc (l : Loc) (dq : DFrac) (m : GoMap) :
    (l ↦{dq} ({ buckets' := m } : txBuffer) : IProp GF) ⊢
      structFieldRef txBuffer go!"buckets" l ↦{dq} m ∗
      (structFieldRef txBuffer go!"buckets" l ↦{dq} m -∗
        l ↦{dq} ({ buckets' := m } : txBuffer)) := by
  iintro H
  icases typedPointsto_not_null_dup _ _ _ $$ H with ⟨H, %Hnn⟩
  iStructNamed H
  iframe buckets
  iintro Hb
  iapply typedPointsto_combine _ _ _ Hnn
  simp only [TypedPointsto.typedPointstoDef]
  iframe

/-! ## A bucket buffer -/

theorem bbAt_not_null (bb : Loc) (dq : DFrac) (p : BBPhys) (es : List Ent) :
    bbAt (GF := GF) bb dq p es ⊢ ⌜bb ≠ null⌝ := by
  iintro H
  unfold bbAt
  icases H with ⟨H, -⟩
  iapply typedPointsto_not_null _ _ _ $$ H

/-- No entries in the first slots. -/
theorem entsIn_nil (kvs : List kv) : ⊢ entsIn (GF := GF) kvs [] := by
  unfold entsIn
  isplitr
  · ipureintro; exact Nat.zero_le _
  · rw [List.zip_nil_right]
    iapply (BigSepL.bigSepL_nil (PROP := IProp GF)).2
    iempintro

/-- An empty buffer (its `used` zero), from its fields. -/
theorem bbAt_nil_intro (bb : Loc) (dq : DFrac) (p : BBPhys) :
    (bb ↦{dq} ({ buf' := p.buf, used' := W64 0 } : bucketBuffer) : IProp GF) -∗
      p.buf ↦*{dq} p.kvs -∗ ownSliceCap kv p.buf dq -∗ slotsRO (GF := GF) p.kvs -∗
      bbAt bb dq p [] := by
  iintro Hbb Hs Hcap #Hro
  unfold bbAt
  iframe Hbb Hs Hcap Hro
  iapply entsIn_nil

/-! ## The buffers of a buckets map -/

/-- The buffers' layout and the entries have the same buckets. -/
theorem bbs_lookup_iff (P : BksPhys) (B : GMap w64 (List Ent)) (dq : DFrac) :
    ([∗map] _id ↦ x;es ∈ P;B, bbAt (GF := GF) x.1 dq x.2 es) ⊢
      ⌜∀ k, (P !! k).isSome ↔ (B !! k).isSome⌝ :=
  BigSepM2.bigSepM2_lookup_iff

/-- A bucket of the layout is a bucket of the entries. -/
theorem bbs_lookup_some (P : BksPhys) (B : GMap w64 (List Ent)) (dq : DFrac) (id : w64)
    (x : Loc × BBPhys) (h : P !! id = some x) :
    ([∗map] _id ↦ x;es ∈ P;B, bbAt (GF := GF) x.1 dq x.2 es) ⊢
      ⌜∃ es, B !! id = some es⌝ := by
  iintro H
  ihave %Hiff := bbs_lookup_iff P B dq $$ H
  ipureintro
  have := (Hiff id).1 (by rw [h]; rfl)
  exact Option.isSome_iff_exists.1 this

/-- A bucket absent from the layout is absent from the entries. -/
theorem bbs_lookup_none (P : BksPhys) (B : GMap w64 (List Ent)) (dq : DFrac) (id : w64)
    (h : P !! id = none) :
    ([∗map] _id ↦ x;es ∈ P;B, bbAt (GF := GF) x.1 dq x.2 es) ⊢ ⌜B !! id = none⌝ := by
  iintro H
  ihave %Hiff := bbs_lookup_iff P B dq $$ H
  ipureintro
  cases hb : B !! id with
  | none => rfl
  | some _ =>
    have := (Hiff id).2 (by rw [hb]; rfl)
    rw [h] at this; cases this

/-- A bucket absent from the entries is absent from the layout. -/
theorem bbs_lookup_none_r (P : BksPhys) (B : GMap w64 (List Ent)) (dq : DFrac) (id : w64)
    (h : B !! id = none) :
    ([∗map] _id ↦ x;es ∈ P;B, bbAt (GF := GF) x.1 dq x.2 es) ⊢ ⌜P !! id = none⌝ := by
  iintro H
  ihave %Hiff := bbs_lookup_iff P B dq $$ H
  ipureintro
  cases hp : P !! id with
  | none => rfl
  | some _ =>
    have := (Hiff id).1 (by rw [hp]; rfl)
    rw [h] at this; cases this

/-- One buffer out and the rest over the maps without it. -/
theorem bbs_delete (P : BksPhys) (B : GMap w64 (List Ent)) (dq : DFrac) (id : w64)
    (x : Loc × BBPhys) (es : List Ent) (hP : P !! id = some x) (hB : B !! id = some es) :
    ([∗map] _id ↦ x;es ∈ P;B, bbAt (GF := GF) x.1 dq x.2 es) ⊣⊢
      bbAt x.1 dq x.2 es ∗
        [∗map] _id ↦ x;es ∈ (GMap.delete id P : BksPhys);(GMap.delete id B : GMap w64 (List Ent)), bbAt (GF := GF) x.1 dq x.2 es :=
  BigSepM2.bigSepM2_delete (Φ := fun _ (x : Loc × BBPhys) (es : List Ent) => bbAt (GF := GF) x.1 dq x.2 es) hP hB

/-- A new buffer in. -/
theorem bbs_insert (P : BksPhys) (B : GMap w64 (List Ent)) (dq : DFrac) (id : w64)
    (x : Loc × BBPhys) (es : List Ent) (hP : P !! id = none) (hB : B !! id = none) :
    ([∗map] _id ↦ x;es ∈ (<[id := x]> P : BksPhys);(<[id := es]> B : GMap w64 (List Ent)), bbAt (GF := GF) x.1 dq x.2 es) ⊣⊢
      bbAt x.1 dq x.2 es ∗ [∗map] _id ↦ x;es ∈ P;B, bbAt (GF := GF) x.1 dq x.2 es :=
  BigSepM2.bigSepM2_insert (Φ := fun _ (x : Loc × BBPhys) (es : List Ent) => bbAt (GF := GF) x.1 dq x.2 es) hP hB

/-- A buffer of the map, and the map back with that buffer changed (its layout `x'` and entries
`es'`). -/
theorem bbs_insert_acc (P : BksPhys) (B : GMap w64 (List Ent)) (dq : DFrac) (id : w64)
    (x : Loc × BBPhys) (hP : P !! id = some x) :
    ([∗map] _id ↦ x;es ∈ P;B, bbAt (GF := GF) x.1 dq x.2 es) ⊢
      ∃ es, ⌜B !! id = some es⌝ ∗ bbAt x.1 dq x.2 es ∗
        ∀ (x' : Loc × BBPhys) (es' : List Ent), bbAt x'.1 dq x'.2 es' -∗
          [∗map] _id ↦ x;es ∈ (<[id := x']> P : BksPhys);(<[id := es']> B : GMap w64 (List Ent)), bbAt (GF := GF) x.1 dq x.2 es := by
  iintro H
  ihave %Hs := bbs_lookup_some P B dq id x hP $$ H
  obtain ⟨es, hB⟩ := Hs
  icases BigSepM2.bigSepM2_insert_acc (Φ := fun _ (x : Loc × BBPhys) (es : List Ent) => bbAt (GF := GF) x.1 dq x.2 es)
    (m1 := P) (m2 := B) hP hB $$ H with ⟨Hb, Hback⟩
  iexists es
  iframe Hb
  isplitr
  · ipureintro; exact hB
  iintro %x' %es' Hb
  iapply Hback $$ %x' %es' Hb

/-- A buffer of the map, and the map back with that buffer as it was. -/
theorem bbs_lookup_acc (P : BksPhys) (B : GMap w64 (List Ent)) (dq : DFrac) (id : w64)
    (x : Loc × BBPhys) (hP : P !! id = some x) :
    ([∗map] _id ↦ x;es ∈ P;B, bbAt (GF := GF) x.1 dq x.2 es) ⊢
      ∃ es, ⌜B !! id = some es⌝ ∗ bbAt x.1 dq x.2 es ∗
        (bbAt x.1 dq x.2 es -∗ [∗map] _id ↦ x;es ∈ P;B, bbAt (GF := GF) x.1 dq x.2 es) := by
  iintro H
  ihave %Hs := bbs_lookup_some P B dq id x hP $$ H
  obtain ⟨es, hB⟩ := Hs
  icases BigSepM2.bigSepM2_lookup_acc (Φ := fun _ (x : Loc × BBPhys) (es : List Ent) => bbAt (GF := GF) x.1 dq x.2 es)
    (m1 := P) (m2 := B) hP hB $$ H with ⟨Hb, Hback⟩
  iexists es
  iframe Hb Hback
  ipureintro; exact hB

/-- No buffers. -/
theorem bbs_empty (dq : DFrac) :
    ⊢ [∗map] _id ↦ x;es ∈ (∅ : BksPhys);(∅ : GMap w64 (List Ent)), bbAt (GF := GF) x.1 dq x.2 es := by
  iapply (BigSepM2.bigSepM2_empty _).2
  iempintro

/-! ## Results -/

/-- `nil, nil`: no entries. -/
theorem kvsOut_nil : ⊢ kvsOut (GF := GF) slice.nil slice.nil [] := by
  unfold kvsOut slicesAre
  iexists [], []
  simp only [List.map_nil, List.zip_nil_left, List.length_nil]
  isplitr
  · iapply ownSlice_nil
  isplitr
  · iapply ownSliceCap_nil
  isplitr
  · iapply ownSlice_nil
  isplitr
  · iapply ownSliceCap_nil
  isplitr
  · isplitr
    · ipureintro; trivial
    · iapply (BigSepL.bigSepL_nil (PROP := IProp GF)).2; iempintro
  · isplitr
    · ipureintro; trivial
    · iapply (BigSepL.bigSepL_nil (PROP := IProp GF)).2; iempintro

end lemmas

end backend
end EtcdGrove
end Perennial

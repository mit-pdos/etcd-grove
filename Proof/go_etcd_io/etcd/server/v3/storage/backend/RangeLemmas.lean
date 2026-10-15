/-
Lemmas for the proofs of the bucket buffer's readers and `sort.Interface` methods
(`bucketBuffer.{Range,ForEach,Len,Less,Swap,CopyUsed}`): `bytes.Compare`'s result, the slots
of a buffer (`entsIn`, `slotsRO`) under a swap and a lookup, and `bbRange` as the loop of
`Range` computes it. Lean-first (no Rocq counterpart).
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

/-! ## `bytes.Compare` -/

theorem compareResult_lt_iff (a b : GoString) :
    sint.Z (bytes.compareResult a b) < 0 ↔ strLt a b := by
  unfold bytes.compareResult
  by_cases h : go.GoStringLt a b
  · simp only [h, ↓reduceIte, iff_true]; decide
  · simp only [h, ↓reduceIte, iff_false]
    split <;> decide

theorem compareResult_gt_iff (a b : GoString) :
    0 < sint.Z (bytes.compareResult a b) ↔ strLt b a := by
  unfold bytes.compareResult
  by_cases h : go.GoStringLt a b
  · simp only [h, ↓reduceIte]
    exact ⟨fun h' => absurd h' (by decide), fun h' => absurd h' (strLt_asymm h)⟩
  · simp only [h, ↓reduceIte]
    by_cases he : a = b
    · subst he; simp only [↓reduceIte]
      exact ⟨fun h' => absurd h' (by decide), fun h' => absurd h' (strLt_irrefl a)⟩
    · simp only [he, ↓reduceIte]
      refine ⟨fun _ => ?_, fun _ => by decide⟩
      exact Classical.byContradiction fun h' => he (strLt_eq_of_not_lt h h')

/-- `bytes.Compare(a, b) < 0` is `a < b`. -/
theorem compareResult_neg (a b : GoString) :
    decide (sint.Z (bytes.compareResult a b) < sint.Z (W64 0)) = decide (strLt a b) := by
  apply decide_eq_decide.2
  rw [← compareResult_lt_iff]; exact Iff.rfl

/-- `bytes.Compare(a, b) >= 0` is `!(a < b)`. -/
theorem compareResult_ge (a b : GoString) :
    decide (sint.Z (bytes.compareResult a b) ≥ sint.Z (W64 0)) = !decide (strLt a b) := by
  rw [← compareResult_neg]
  by_cases h : sint.Z (bytes.compareResult a b) < sint.Z (W64 0)
  · rw [_root_.decide_eq_true h, _root_.decide_eq_false (by omega)]; rfl
  · rw [_root_.decide_eq_false h, _root_.decide_eq_true (by omega)]; rfl

/-- `bytes.Compare(a, b) <= 0` is `!(b < a)`. -/
theorem compareResult_le (a b : GoString) :
    decide (sint.Z (bytes.compareResult a b) ≤ sint.Z (W64 0)) = !decide (strLt b a) := by
  have := compareResult_gt_iff a b
  by_cases h : strLt b a
  · rw [_root_.decide_eq_true h, _root_.decide_eq_false (by
      have := this.2 h; show ¬ sint.Z _ ≤ 0; omega)]; rfl
  · rw [_root_.decide_eq_false h, _root_.decide_eq_true (by
      have := mt this.1 h; show sint.Z _ ≤ 0; omega)]; rfl

/-! ## Swapping two elements of a list -/

/-- The index a swap of `i` and `j` reads position `k` from. -/
def swapIdx (i j k : Nat) : Nat := if k = i then j else if k = j then i else k

/-- `l[j] := l[i]`, then `l[i] := l[j]`. -/
theorem swap_getElem? {α : Type} (l : List α) (i j : Nat) (x y : α)
    (hx : l[i]? = some x) (hy : l[j]? = some y) (k : Nat) :
    ((l.set j x).set i y)[k]? = l[swapIdx i j k]? := by
  have hi : i < l.length := (List.getElem?_eq_some_iff.1 hx).1
  have hj : j < l.length := (List.getElem?_eq_some_iff.1 hy).1
  unfold swapIdx
  rw [List.getElem?_set, List.getElem?_set]
  by_cases hki : k = i
  · subst hki
    simp only [ite_true, List.length_set, hi, hy]
  · simp only [hki, ite_false, Ne.symm hki]
    by_cases hkj : k = j
    · subst hkj; simp only [ite_true, hj, hx]
    · simp only [hkj, ite_false, Ne.symm hkj]

/-- `l[i] := l[j]`, then `l[j] := l[i]` (`Swap`'s slots, and the spec's entries). -/
theorem swap_getElem?' {α : Type} (l : List α) (i j : Nat) (x y : α)
    (hx : l[i]? = some x) (hy : l[j]? = some y) (k : Nat) :
    ((l.set i y).set j x)[k]? = l[swapIdx i j k]? := by
  by_cases hij : i = j
  · subst hij
    have : x = y := by rw [hx] at hy; exact Option.some.inj hy
    subst this
    rw [swap_getElem? l i i x x hx hx k]
  · have : (l.set i y).set j x = (l.set j x).set i y := List.set_comm _ _ hij
    rw [this, swap_getElem? l i j x y hx hy k]

theorem swapIdx_lt {i j k n : Nat} (hi : i < n) (hj : j < n) (hk : k < n) : swapIdx i j k < n := by
  unfold swapIdx; split
  · exact hj
  · split
    · exact hi
    · exact hk

/-! ## `dropWhile`, `takeWhile` and `bbRange` -/

/-- `dropWhile` drops the first `m` elements if they satisfy `p` and the next does not. -/
theorem dropWhile_eq_drop {α : Type} (p : α → Bool) (l : List α) (m : Nat) (hm : m ≤ l.length)
    (hall : ∀ (k : Nat) (x : α), k < m → l[k]? = some x → p x = true)
    (hstop : ∀ x, l[m]? = some x → p x = false) :
    l.dropWhile p = l.drop m := by
  induction l generalizing m with
  | nil => simp
  | cons a t ih =>
    cases m with
    | zero =>
      have : p a = false := hstop a rfl
      simp [this]
    | succ m =>
      have ha : p a = true := hall 0 a (by omega) rfl
      rw [List.dropWhile_cons, ha]
      simp only [ite_true, List.drop_succ_cons]
      apply ih m (by simp at hm; omega)
      · intro k x hk hx; exact hall (k + 1) x (by omega) (by simpa using hx)
      · intro x hx; exact hstop x (by simpa using hx)

theorem takeWhile_eq_take_append {α : Type} (p : α → Bool) (l : List α) (m : Nat)
    (hall : ∀ (k : Nat) (x : α), k < m → l[k]? = some x → p x = true) :
    l.takeWhile p = l.take m ++ (l.drop m).takeWhile p := by
  induction l generalizing m with
  | nil => simp
  | cons a t ih =>
    cases m with
    | zero => simp
    | succ m =>
      have ha : p a = true := hall 0 a (by omega) rfl
      rw [List.takeWhile_cons, ha]
      simp only [ite_true, List.take_succ_cons, List.drop_succ_cons, List.cons_append]
      rw [ih m (fun k x hk hx => hall (k + 1) x (by omega) (by simpa using hx))]

/-- The first `lim` of the prefix satisfying `p` are the first `m`, if the first `m` satisfy
`p` (`m ≤ lim`) and the list ends there, the next fails `p`, or `m = lim`: `Range`'s loop
at its exit. -/
theorem takeWhile_take_eq {α : Type} (p : α → Bool) (l : List α) (m lim : Nat)
    (hall : ∀ (k : Nat) (x : α), k < m → l[k]? = some x → p x = true)
    (hle : m ≤ lim)
    (hend : m = l.length ∨ (∃ x, l[m]? = some x ∧ p x = false) ∨ m = lim) :
    (l.takeWhile p).take lim = l.take m := by
  rw [takeWhile_eq_take_append p l m hall]
  rcases hend with h | ⟨x, hx, hpx⟩ | h
  · subst h
    simp only [List.drop_length, List.takeWhile_nil, List.append_nil, List.take_length]
    exact List.take_of_length_le hle
  · rw [List.drop_eq_getElem_cons (List.getElem?_eq_some_iff.1 hx).1]
    have : l[m]'(List.getElem?_eq_some_iff.1 hx).1 = x := (List.getElem?_eq_some_iff.1 hx).2
    rw [List.takeWhile_cons, this, hpx]
    simp only [Bool.false_eq_true, ite_false, List.append_nil]
    rw [List.take_take]; congr 1; omega
  · subst h
    by_cases hm : m ≤ l.length
    · rw [List.take_append_of_le_length (by simp; omega)]
      rw [List.take_take, Nat.min_self]
    · rw [List.take_of_length_le (l := l) (by omega), List.drop_of_length_le (by omega)]
      simp only [List.takeWhile_nil, List.append_nil]
      exact List.take_of_length_le (by omega)

/-- `bbRange` when every entry is below `key`. -/
theorem bbRange_of_dropWhile_nil (es : List Ent) (key endKey : GoString) (limit : w64)
    (h : es.dropWhile (fun e => decide (strLt e.1 key)) = []) :
    bbRange es key endKey limit = [] := by
  unfold bbRange; rw [h]

/-- `bbRange` from the first entry not below `key`. -/
theorem bbRange_of_dropWhile_cons (es : List Ent) (key endKey : GoString) (limit : w64)
    (e : Ent) (rest : List Ent)
    (h : es.dropWhile (fun e => decide (strLt e.1 key)) = e :: rest) :
    bbRange es key endKey limit =
      if endKey = [] then (if e.1 = key then [e] else [])
      else ((e :: rest).takeWhile (fun e => decide (strLt e.1 endKey))).take
        (sint.Z limit).toNat := by
  unfold bbRange; rw [h]

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

/-! ## A bucket buffer's fields -/

/-- The fields of a bucket buffer at any fraction (`wp_load` finds a field of a struct
points-to only at fraction 1), and back. -/
theorem bb_fields_acc (l : Loc) (v : bucketBuffer) (dq : DFrac) :
    (l ↦{dq} v : IProp GF) ⊢
      structFieldRef bucketBuffer go!"buf" l ↦{dq} v.buf' ∗
      structFieldRef bucketBuffer go!"used" l ↦{dq} v.used' ∗
      (structFieldRef bucketBuffer go!"buf" l ↦{dq} v.buf' -∗
        structFieldRef bucketBuffer go!"used" l ↦{dq} v.used' -∗ l ↦{dq} v) := by
  iintro H
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ H
  iStructNamed H
  iframe buf used
  iintro Hb Hu
  iapply typedPointsto_combine _ _ _ Hnn
  simp only [TypedPointsto.typedPointstoDef]
  iframe Hb Hu

/-- A slot's key, loaded from the buffer's slice at any fraction. -/
theorem wp_load_slot_key (sl : GoSlice) (i : Int) (kvs : List kv) (dq : DFrac) (x : kv)
    (hpos : 0 ≤ i) (h : kvs[i.toNat]? = some x) :
    {{ (sl ↦*{dq} kvs : IProp GF) }}
      (App (Val (GoInstruction (GoLoad (go.GoType.SliceType go.byte))))
        (Val #(structFieldRef kv go!"key" (sliceIndexRef kv i sl))))
    {{ RET #x.key'; sl ↦*{dq} kvs }} := by
  iintro %Φ Hs HΦ
  icases ownSlice_elem_acc i x sl dq kvs hpos h $$ Hs with ⟨Hel, Hback⟩
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hel
  iStructNamed Hel
  wp_apply IntoValTyped.wp_load (t := go.GoType.SliceType go.byte) _ _ _ $$ key as key
  iapply HΦ
  ihave Hel : (sliceIndexRef kv i sl ↦{dq} x : IProp GF) $$ [key val]
  · iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe key val
  ihave Hs := Hback $$ Hel
  rw [list_set_lookup_self kvs i.toNat x h]
  iexact Hs

/-- A slot's value, loaded from the buffer's slice at any fraction. -/
theorem wp_load_slot_val (sl : GoSlice) (i : Int) (kvs : List kv) (dq : DFrac) (x : kv)
    (hpos : 0 ≤ i) (h : kvs[i.toNat]? = some x) :
    {{ (sl ↦*{dq} kvs : IProp GF) }}
      (App (Val (GoInstruction (GoLoad (go.GoType.SliceType go.byte))))
        (Val #(structFieldRef kv go!"val" (sliceIndexRef kv i sl))))
    {{ RET #x.val'; sl ↦*{dq} kvs }} := by
  iintro %Φ Hs HΦ
  icases ownSlice_elem_acc i x sl dq kvs hpos h $$ Hs with ⟨Hel, Hback⟩
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hel
  iStructNamed Hel
  wp_apply IntoValTyped.wp_load (t := go.GoType.SliceType go.byte) _ _ _ $$ val as val
  iapply HΦ
  ihave Hel : (sliceIndexRef kv i sl ↦{dq} x : IProp GF) $$ [key val]
  · iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe key val
  ihave Hs := Hback $$ Hel
  rw [list_set_lookup_self kvs i.toNat x h]
  iexact Hs

/-! ## The slots of a buffer -/

/-- The slot of the `n`-th entry holds its key and value. -/
theorem entsIn_lookup (kvs : List kv) (es : List Ent) (n : Nat) (x : kv) (e : Ent)
    (hx : kvs[n]? = some x) (he : es[n]? = some e) :
    entsIn (GF := GF) kvs es ⊢ x.key' ↦*□ e.1 ∗ x.val' ↦*□ e.2 := by
  unfold entsIn
  iintro ⟨_, H⟩
  have hz : (kvs.zip es)[n]? = some (x, e) := List.getElem?_zip_eq_some.2 ⟨hx, he⟩
  iapply (BigSepL.bigSepL_lookup (Φ := fun _ (y : kv × Ent) =>
    iprop(y.1.key' ↦*□ y.2.1 ∗ y.1.val' ↦*□ y.2.2)) hz) $$ H

/-- Every slot's key and value slices are read-only. -/
theorem slotsRO_lookup (kvs : List kv) (n : Nat) (x : kv) (hx : kvs[n]? = some x) :
    slotsRO (GF := GF) kvs ⊢ ∃ (b1 b2 : GoString), x.key' ↦*□ b1 ∗ x.val' ↦*□ b2 := by
  unfold slotsRO
  iintro H
  iapply (BigSepL.bigSepL_lookup (Φ := fun _ (y : kv) =>
    iprop(∃ (b1 b2 : GoString), y.key' ↦*□ b1 ∗ y.val' ↦*□ b2)) hx) $$ H

/-- Fresh slots (zero values: nil slices) are read-only. -/
theorem slotsRO_replicate_zero (n : Nat) :
    ⊢ slotsRO (GF := GF) (List.replicate n (zero_val kv)) := by
  unfold slotsRO
  have hall : ∀ (k : Nat) (x : kv), (List.replicate n (zero_val kv))[k]? = some x →
      iprop(□ (slice.nil ↦*□ ([] : List w8))) ⊢
        iprop(∃ (b1 b2 : GoString), x.key' ↦*□ b1 ∗ x.val' ↦*□ b2 : IProp GF) := by
    intro k x hk
    rw [List.getElem?_replicate] at hk
    split at hk
    · cases hk
      iintro #H'
      iexists [], []
      iframe # ∗
    · cases hk
  iintro
  ihave #H := ownSlice_nil (GF := GF) (V := w8) DFrac.discard
  iapply (BigSepL.bigSepL_intro hall)
  imodintro; iexact H

/-- No entries are in any slots. -/
theorem entsIn_nil_r (kvs : List kv) : ⊢ entsIn (GF := GF) kvs [] := by
  unfold entsIn
  simp only [List.zip_nil_right]
  iintro
  isplitr
  · ipureintro; exact Nat.zero_le _
  iapply BigSepL.bigSepL_nil.2; iempintro

/-- A list's big separating conjunction of a persistent predicate holds of any list whose
elements are all elements of it. -/
theorem bigSepL_of_lookups {A : Type} (Φ : A → IProp GF) [∀ x, Persistent (Φ x)]
    (l l' : List A) (hl : ∀ (k : Nat) (x : A), l'[k]? = some x → ∃ k' : Nat, l[k']? = some x) :
    ([∗list] x ∈ l, Φ x) ⊢ [∗list] x ∈ l', Φ x := by
  refine (BigSepL.bigSepL_forall_eqv (Φ := fun _ x => Φ x)).1.trans ?_
  refine BIBase.Entails.trans ?_ (BigSepL.bigSepL_forall_eqv (Φ := fun _ x => Φ x)).2
  iintro #H %k %x %hk
  obtain ⟨k', hk'⟩ := hl k x hk
  iapply H $$ %k' %x %hk'

/-- `slotsRO` after a swap of two slots (as `Swap` stores them: `i` first). -/
theorem slotsRO_swap (kvs : List kv) (i j : Nat) (x y : kv)
    (hx : kvs[i]? = some x) (hy : kvs[j]? = some y) :
    slotsRO (GF := GF) kvs ⊢ slotsRO ((kvs.set i y).set j x) := by
  unfold slotsRO
  apply bigSepL_of_lookups
  intro k z hk
  exact ⟨swapIdx i j k, by rw [← swap_getElem?' kvs i j x y hx hy k]; exact hk⟩

/-- `entsIn` after a swap of two slots among the entries' and the same swap of the entries. -/
theorem entsIn_swap (kvs : List kv) (es : List Ent) (i j : Nat) (x y : kv) (a b : Ent)
    (hx : kvs[i]? = some x) (hy : kvs[j]? = some y) (ha : es[i]? = some a)
    (hb : es[j]? = some b) :
    entsIn (GF := GF) kvs es ⊢ entsIn ((kvs.set i y).set j x) ((es.set i b).set j a) := by
  unfold entsIn
  iintro ⟨%Hle, H⟩
  isplitr
  · ipureintro; simp only [List.length_set]; exact Hle
  iapply (bigSepL_of_lookups (fun (z : kv × Ent) =>
    iprop(z.1.key' ↦*□ z.2.1 ∗ z.1.val' ↦*□ z.2.2)) _ _ ?_) $$ H
  intro k z hk
  refine ⟨swapIdx i j k, ?_⟩
  obtain ⟨z1, z2⟩ := z
  rw [List.getElem?_zip_eq_some] at hk ⊢
  rw [swap_getElem?' kvs i j x y hx hy k] at hk
  rw [swap_getElem?' es i j a b ha hb k] at hk
  exact hk

/-- The first `n` slots of a buffer's are read-only. -/
theorem slotsRO_take (kvs : List kv) (n : Nat) :
    slotsRO (GF := GF) kvs ⊢ slotsRO (kvs.take n) := by
  unfold slotsRO
  apply bigSepL_of_lookups
  intro k x hk
  rw [List.getElem?_take] at hk
  split at hk
  · exact ⟨k, hk⟩
  · cases hk

/-- The first `n` slots hold the entries, if there are at most `n`. -/
theorem entsIn_take_kvs (kvs : List kv) (es : List Ent) (n : Nat) (hn : es.length ≤ n) :
    entsIn (GF := GF) kvs es ⊢ entsIn (kvs.take n) es := by
  unfold entsIn
  iintro ⟨%Hle, H⟩
  isplitr
  · ipureintro; simp only [List.length_take]; omega
  iapply (bigSepL_of_lookups (fun (z : kv × Ent) =>
    iprop(z.1.key' ↦*□ z.2.1 ∗ z.1.val' ↦*□ z.2.2)) _ _ ?_) $$ H
  intro k z hk
  refine ⟨k, ?_⟩
  obtain ⟨z1, z2⟩ := z
  rw [List.getElem?_zip_eq_some] at hk ⊢
  refine ⟨?_, hk.2⟩
  have h1 := hk.1
  rw [List.getElem?_take] at h1
  split at h1
  · exact h1
  · cases h1

/-! ## `Range`'s results -/

theorem slicesAre_nil : ⊢ slicesAre (GF := GF) [] [] := by
  unfold slicesAre
  simp only [List.zip_nil_left]
  iintro
  isplitr
  · ipureintro; rfl
  iapply BigSepL.bigSepL_nil.2; iempintro

theorem slicesAre_snoc (ss : List GoSlice) (bs : List GoString) (s : GoSlice) (b : GoString) :
    slicesAre (GF := GF) ss bs ∗ s ↦*□ b ⊢ slicesAre (ss ++ [s]) (bs ++ [b]) := by
  unfold slicesAre
  iintro ⟨⟨%Hlen, H⟩, #Hs⟩
  isplitr
  · ipureintro; simp [Hlen]
  rw [List.zip_append Hlen]
  iapply BigSepL.bigSepL_append.2
  iframe H
  simp only [List.zip_cons_cons, List.zip_nil_left]
  iapply BigSepL.bigSepL_singleton.2
  iexact Hs

/-- No results: the nil slices. -/
theorem kvsOut_nil_r : ⊢ kvsOut (GF := GF) slice.nil slice.nil [] := by
  unfold kvsOut
  iintro
  ihave Hk := ownSlice_nil (GF := GF) (V := GoSlice) (DFrac.own 1)
  ihave Hv := ownSlice_nil (GF := GF) (V := GoSlice) (DFrac.own 1)
  ihave Hkc := ownSliceCap_nil (GF := GF) (V := GoSlice)
  ihave Hvc := ownSliceCap_nil (GF := GF) (V := GoSlice)
  ihave Hs1 := slicesAre_nil (GF := GF)
  ihave Hs2 := slicesAre_nil (GF := GF)
  iexists [], []
  simp only [List.map_nil]
  isplitr
  · iexact Hk
  isplitr
  · iexact Hkc
  isplitr
  · iexact Hv
  isplitr
  · iexact Hvc
  isplitr
  · iexact Hs1
  iexact Hs2

end defs

end backend
end EtcdGrove
end Perennial

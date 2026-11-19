/-
**Deep copies: the lemmas of the generated proofs** of deepcopy-gen's `DeepCopyInto` methods
(`Proof/k8s_io/api/DeepCopy/`, `etc/gen-k8s-deep.py`), over the deep ownership of
`Proof/k8s_io/api/DeepBase.lean`. Lean-first (no Rocq counterpart).

Each generated proof copies the struct (`*out = *in`), splits both struct points-tos into fields
and then follows deepcopy-gen's blocks, one per field that is not copied with the struct: for a
pointer, slice or map field, `if in.F != nil { ... }`, whose two cases are joined
(`wp_join`) at "the copy's field owns the field's deep value at fraction 1". These lemmas turn the
ownership of a field into the facts each case needs (`nil` or not, and what it points to) and
back.
-/
module

public import Proof.k8s_io.api.DeepBase

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-! ### Pointers -/

theorem ownPtrD_null {V E : Type} [ZeroVal V] [TypedPointsto (GF := GF) V]
    (inner : V → DFrac → E → IProp GF) (dq : DFrac) (e : Option E) :
    ownPtrD inner null dq e ⊢ ⌜e = none⌝ := by
  cases e with
  | none => iintro -; ipureintro; rfl
  | some e =>
    unfold ownPtrD
    iintro ⟨%x, Hp, -⟩
    ihave %h := typedPointsto_not_null _ _ _ $$ Hp
    exact absurd rfl h

theorem ownPtrD_nonnull {V E : Type} [ZeroVal V] [TypedPointsto (GF := GF) V]
    (inner : V → DFrac → E → IProp GF) (p : Loc) (dq : DFrac) (e : Option E) (h : p ≠ null) :
    ownPtrD inner p dq e ⊢ ∃ x e', ⌜e = some e'⌝ ∗ p ↦{dq} x ∗ inner x dq e' := by
  cases e with
  | none => unfold ownPtrD; iintro %h'; exact absurd h' h
  | some e =>
    unfold ownPtrD
    iintro ⟨%x, Hp, Hx⟩
    iexists x, e
    iframe
    ipureintro; rfl

theorem ownPtrD_some {V E : Type} [ZeroVal V] [TypedPointsto (GF := GF) V]
    (inner : V → DFrac → E → IProp GF) (p : Loc) (dq : DFrac) (x : V) (e : E) :
    p ↦{dq} x ∗ inner x dq e ⊢ ownPtrD inner p dq (some e) := by
  unfold ownPtrD
  iintro ⟨Hp, Hx⟩
  iexists x
  iframe

theorem ownPtrD_none {V E : Type} [ZeroVal V] [TypedPointsto (GF := GF) V]
    (inner : V → DFrac → E → IProp GF) (dq : DFrac) :
    ⊢ ownPtrD inner null dq (none : Option E) := by
  unfold ownPtrD; ipureintro; rfl

theorem ownPtrD_null_dup {V E : Type} [ZeroVal V] [TypedPointsto (GF := GF) V]
    (inner : V → DFrac → E → IProp GF) (p : Loc) (dq dq' : DFrac) (e : Option E) (h : p = null) :
    ownPtrD inner p dq e ⊢ ownPtrD inner p dq e ∗ ownPtrD inner p dq' e := by
  subst h
  iintro H
  ihave %he := ownPtrD_null inner dq e $$ H
  subst he
  unfold ownPtrD
  isplitr <;> ipureintro <;> rfl

/-! ### Fields that must be nil -/

theorem ownNilPtrD_null (p : Loc) : ownNilPtrD (GF := GF) p ⊢ ⌜p = null⌝ := by
  unfold ownNilPtrD; iintro %h; ipureintro; exact h
theorem ownNilSliceD_null (s : GoSlice) : ownNilSliceD (GF := GF) s ⊢ ⌜s = slice.nil⌝ := by
  unfold ownNilSliceD; iintro %h; ipureintro; exact h
theorem ownNilMapD_null (m : GoMap) : ownNilMapD (GF := GF) m ⊢ ⌜m = null⌝ := by
  unfold ownNilMapD; iintro %h; ipureintro; exact h
theorem ownNilIfaceD_null (i : GoInterface) : ownNilIfaceD (GF := GF) i ⊢ ⌜i = interface.nil⌝ := by
  unfold ownNilIfaceD; iintro %h; ipureintro; exact h

/-! ### Fraction-free ownership (basic values, structs of them) -/

/-- **A fraction-free deep ownership**: persistent, and the same at every fraction (the deep
ownership of a value with no pointer, slice or map: copied with its struct). -/
class DeepFree {V E : Type} (inner : V → DFrac → E → IProp GF) : Prop where
  persistent : ∀ x dq e, Persistent (inner x dq e)
  frac : ∀ x dq dq' e, inner x dq e ⊢ inner x dq' e

instance ownBaseD_deepFree {V : Type} : DeepFree (GF := GF) (ownBaseD (V := V)) where
  persistent := by intro x dq e; infer_instance
  frac := by intro x dq dq' e; unfold ownBaseD; iintro %h; ipureintro; exact h

theorem deepFree_dup {V E : Type} (inner : V → DFrac → E → IProp GF) [hI : DeepFree inner]
    (x : V) (dq dq' : DFrac) (e : E) :
    inner x dq e ⊢ inner x dq e ∗ inner x dq' e := by
  haveI := hI.persistent x dq e
  iintro #H
  isplitr
  · iexact H
  · iapply hI.frac x dq dq' e $$ H

theorem bigSepL2_deepFree_dup {V E : Type} (inner : V → DFrac → E → IProp GF) [hI : DeepFree inner]
    (dq dq' : DFrac) : ∀ (vs : List V) (es : List E),
      ([∗list] x;e ∈ vs;es, inner x dq e) ⊢
        ([∗list] x;e ∈ vs;es, inner x dq e) ∗ [∗list] x;e ∈ vs;es, inner x dq' e
  | [], [] => by
    iintro H
    isplitl [H]
    · iexact H
    · iapply (BigSepL2.bigSepL2_nil (PROP := IProp GF)).2; iempintro
  | [], _ :: _ => by iintro H; ihave %h := BigSepL2.bigSepL2_nil_inv_left $$ H; cases h
  | _ :: _, [] => by iintro H; ihave %h := BigSepL2.bigSepL2_nil_inv_right $$ H; cases h
  | x :: vs, e :: es => by
    iintro ⟨Hx, Hrest⟩
    icases deepFree_dup inner x dq dq' e $$ Hx with ⟨Hx, Hx'⟩
    icases bigSepL2_deepFree_dup inner dq dq' vs es $$ Hrest with ⟨Hrest, Hrest'⟩
    isplitl [Hx Hrest]
    · iframe
    · iframe

/-! ### Slices -/

theorem ownSliceD_nil {V E : Type} [ZeroVal V] [TypedPointsto (GF := GF) V]
    (inner : V → DFrac → E → IProp GF) (dq : DFrac) (es : List E) :
    ownSliceD inner slice.nil dq es ⊢ ⌜es = []⌝ := by
  unfold ownSliceD
  iintro ⟨%vs, Hs, Hl⟩
  ihave %hlen := ownSlice_len _ _ _ $$ Hs
  have hvs : vs = [] := by
    have := hlen.1
    simp [slice.nil] at this
    exact List.length_eq_zero_iff.mp this
  subst hvs
  ihave %h := BigSepL2.bigSepL2_nil_inv_left $$ Hl
  ipureintro; exact h

theorem ownSliceD_nil_dup {V E : Type} [ZeroVal V] [TypedPointsto (GF := GF) V]
    (inner : V → DFrac → E → IProp GF) (s : GoSlice) (dq dq' : DFrac) (es : List E)
    (h : s = slice.nil) :
    ownSliceD inner s dq es ⊢ ownSliceD inner s dq es ∗ ownSliceD inner s dq' es := by
  subst h
  iintro H
  ihave %he := ownSliceD_nil inner dq es $$ H
  subst he
  isplitl [H]
  · iexact H
  · iapply ownSliceD_nil_of; rfl

theorem ownSliceD_elim {V E : Type} [ZeroVal V] [TypedPointsto (GF := GF) V]
    (inner : V → DFrac → E → IProp GF) (s : GoSlice) (dq : DFrac) (es : List E) :
    ownSliceD inner s dq es ⊢ ∃ vs, s ↦*{dq} vs ∗ [∗list] x;e ∈ vs;es, inner x dq e := by
  unfold ownSliceD; iintro H; iexact H

/-- What `copy(make([]T, len(s)), s)` leaves in the new slice: `s`'s elements. -/
theorem list_copy_replicate {A : Type} (vs : List A) (n : Nat) (z : A) (h : vs.length = n) :
    vs.take (List.replicate n z).length ++ (List.replicate n z).drop vs.length = vs := by
  subst h
  simp

theorem ownSliceD_intro {V E : Type} [ZeroVal V] [TypedPointsto (GF := GF) V]
    (inner : V → DFrac → E → IProp GF) (s : GoSlice) (dq : DFrac) (vs : List V) (es : List E) :
    s ↦*{dq} vs ∗ ([∗list] x;e ∈ vs;es, inner x dq e) ⊢ ownSliceD inner s dq es := by
  unfold ownSliceD
  iintro ⟨Hs, Hl⟩
  iexists vs
  iframe

/-! ### Maps -/

theorem ownMapD_null {K V : Type} [ZeroVal K] [DecidableEq K] [ZeroVal V] [go.IntoValInj K]
    (dq : DFrac) (e : Option (GMap K V)) :
    ownMapD (GF := GF) null dq e ⊢ ⌜e = none⌝ := by
  cases e with
  | none => iintro -; ipureintro; rfl
  | some M =>
    unfold ownMapD
    iintro H
    ihave %h := ownMap_not_nil _ _ _ $$ H
    exact absurd rfl h

theorem ownMapD_nonnull {K V : Type} [ZeroVal K] [DecidableEq K] [ZeroVal V] [go.IntoValInj K]
    (m : GoMap) (dq : DFrac) (e : Option (GMap K V)) (h : m ≠ null) :
    ownMapD (GF := GF) m dq e ⊢ ∃ M, ⌜e = some M⌝ ∗ m ↦${dq} M := by
  cases e with
  | none => unfold ownMapD; iintro %h'; exact absurd h' h
  | some M =>
    unfold ownMapD
    iintro H
    iexists M
    iframe
    ipureintro; rfl

theorem ownMapD_null_dup {K V : Type} [ZeroVal K] [DecidableEq K] [ZeroVal V] [go.IntoValInj K]
    (m : GoMap) (dq dq' : DFrac) (e : Option (GMap K V)) (h : m = null) :
    ownMapD (GF := GF) m dq e ⊢ ownMapD m dq e ∗ ownMapD m dq' e := by
  subst h
  iintro H
  ihave %he := ownMapD_null dq e $$ H
  subst he
  unfold ownMapD
  isplitr <;> ipureintro <;> rfl

theorem ownMapD_some {K V : Type} [ZeroVal K] [DecidableEq K] [ZeroVal V] [go.IntoValInj K]
    (m : GoMap) (dq : DFrac) (M : GMap K V) :
    m ↦${dq} M ⊢ ownMapD (GF := GF) m dq (some M) := by
  unfold ownMapD; iintro H; iexact H

/-- The keys of `keys` among the first `i`, with `M`'s values: what a copy loop has copied. -/
def mapPrefix {K V : Type} [DecidableEq K] (M : GMap K V) (keys : List K) (i : Nat) : GMap K V :=
  GMap.filter (fun k _ => decide (k ∈ keys.take i)) M

theorem mapPrefix_zero {K V : Type} [DecidableEq K] (M : GMap K V) (keys : List K) :
    mapPrefix M keys 0 = ∅ := by
  apply GMap.map_eq; intro k; simp [mapPrefix]

theorem mapPrefix_succ {K V : Type} [DecidableEq K] (M : GMap K V) (keys : List K) (i : Nat)
    (k : K) (x : V) (hk : keys[i]? = some k) (hx : M !! k = some x) (_hnd : keys.Nodup) :
    mapPrefix M keys (i + 1) = <[k := x]> (mapPrefix M keys i) := by
  apply GMap.map_eq; intro k'
  have hi : i < keys.length := (List.getElem?_eq_some_iff.1 hk).1
  have htake : keys.take (i + 1) = keys.take i ++ [k] := by
    rw [List.take_add_one, hk]; rfl
  by_cases h : k' = k
  · subst h; simp [mapPrefix, htake, hx]
  · rw [GMap.lookup_insert_ne _ _ (Ne.symm h)]
    simp [mapPrefix, htake, h]

theorem mapPrefix_all {K V : Type} [DecidableEq K] (M : GMap K V) (keys : List K)
    (hkeys : ∀ k, k ∈ keys ↔ (M !! k).isSome) :
    mapPrefix M keys keys.length = M := by
  apply GMap.map_eq; intro k
  simp only [mapPrefix, List.take_length, GMap.lookup_filter]
  cases h : M !! k with
  | none => simp
  | some x =>
    have : k ∈ keys := (hkeys k).2 (by simp [h])
    simp [this]

/-- **A map copy loop** (`for key, val := range *in { (*out)[key] = val }`): from an empty map
`m'`, each iteration inserts the visited entry, so the loop ends with `m'` holding `M`. `R` is
what the body needs besides the map (its variables). -/
theorem wp_map_copy_loop {K V : Type} [ZeroVal K] [DecidableEq K] [MapKeys K] [ZeroVal V]
    [go.IntoValInj K] (kt vt : go.GoType) [TypedPointsto (GF := GF) K]
    [IntoValTyped (GF := GF) K kt] (R : IProp GF) (body : GoFunc) (mref m' : Loc) (M : GMap K V)
    (dq : DFrac) (Φ : val → IProp GF) :
    mref ↦${dq} M -∗ m' ↦$ (∅ : GMap K V) -∗ R -∗
    □ (∀ (k : K) (x : V) (M' : GMap K V), ⌜M !! k = some x⌝ -∗ m' ↦$ M' -∗ R -∗
        WP (App (App (Val #body) (Val #k)) (Val #x))
          {{ bv, ⌜bv = executeVal⌝ ∗ m' ↦$ (<[k := x]> M') ∗ R }}) -∗
    (mref ↦${dq} M -∗ m' ↦$ M -∗ R -∗ Φ executeVal) -∗
    WP (App (App (Val (map.forRange kt vt)) (Val #mref)) (Val #body)) {{ Φ }} := by
  iintro Hm Hm' HR #Hbody HΦ
  iapply wp_map_for_range (fun keys i => iprop(∃ M', m' ↦$ M' ∗ R ∗
      ⌜0 ≤ i ∧ M' = mapPrefix M keys i.toNat ∧ keys.Nodup ∧ (∀ k, k ∈ keys ↔ (M !! k).isSome)⌝))
    body kt vt mref M dq Φ $$ Hm
  iintro %keys %Hkeys
  obtain ⟨Hmem, Hsize, Hnd⟩ := Hkeys
  isplitl [Hm' HR]
  · iexists ∅
    iframe
    ipureintro
    exact ⟨Int.le_refl 0, (mapPrefix_zero M keys).symm, Hnd, Hmem⟩
  isplitr
  · imodintro
    iintro %i %key %x %Hkx ⟨%M', Hm', HR, %HM'⟩
    obtain ⟨Hk, Hx⟩ := Hkx
    obtain ⟨hi0, HM', -, -⟩ := HM'
    iapply wp_wand $$ (Hbody $$ %key %x %M' %Hx Hm' HR)
    iintro %bv ⟨%hbv, Hm', HR⟩
    subst hbv
    unfold forMapPostcondition
    iright; ileft
    isplitr
    · ipureintro; rfl
    iexists (<[key := x]> M')
    iframe
    ipureintro
    refine ⟨by omega, ?_, Hnd, Hmem⟩
    have : (i + 1).toNat = i.toNat + 1 := by omega
    rw [this, mapPrefix_succ M keys i.toNat key x Hk Hx Hnd, HM']
  · iintro ⟨%M', Hm', HR, %HM'⟩ Hm
    obtain ⟨-, HM', -, -⟩ := HM'
    have hlen : (GMap.size M : Int).toNat = keys.length := by omega
    rw [hlen, mapPrefix_all M keys Hmem] at HM'
    subst HM'
    iapply HΦ $$ Hm Hm' HR

/-- **A range loop over a slice the loop only reads** (`for i := range s { body }`, the value
loaded each iteration): `P i` holds before the `i`-th iteration, and the body ends normally. -/
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

/-- **A slice copy loop's progress**: the new slice (length `n`) holds the first `j` copies,
owned whole with the first `j` deep values, then zero values. -/
def copyPrefix {V E : Type} [ZeroVal V] [TypedPointsto (GF := GF) V]
    (inner : V → DFrac → E → IProp GF) (s' : GoSlice) (n : Nat) (ds : List E) (j : Nat) :
    IProp GF :=
  iprop(∃ ys : List V, s' ↦* (ys ++ (List.replicate n (zero_val V)).drop j) ∗
    ([∗list] y;e ∈ ys;ds.take j, inner y (DFrac.own 1) e) ∗ ⌜ys.length = j⌝)

theorem copyPrefix_init {V E : Type} [ZeroVal V] [TypedPointsto (GF := GF) V]
    (inner : V → DFrac → E → IProp GF) (s' : GoSlice) (n : Nat) (ds : List E) :
    s' ↦* List.replicate n (zero_val V) ⊢ copyPrefix inner s' n ds 0 := by
  unfold copyPrefix
  iintro Hs
  iexists []
  simp only [List.nil_append, List.drop_zero, List.take_zero, List.length_nil]
  iframe
  isplitl
  · iapply (BigSepL2.bigSepL2_nil (PROP := IProp GF)).2; iempintro
  · ipureintro; simp

theorem copyPrefix_done {V E : Type} [ZeroVal V] [TypedPointsto (GF := GF) V]
    (inner : V → DFrac → E → IProp GF) (s' : GoSlice) (n : Nat) (ds : List E)
    (hn : ds.length = n) :
    copyPrefix inner s' n ds n ⊢ ownSliceD inner s' (DFrac.own 1) ds := by
  unfold copyPrefix ownSliceD
  iintro ⟨%ys, Hs, Hl, %hys⟩
  iexists ys
  have h1 : (List.replicate n (zero_val V)).drop n = [] := by simp
  have h2 : ds.take n = ds := by rw [← hn]; exact List.take_length
  rw [h1, List.append_nil, h2]
  iframe

/-- **One iteration of a slice copy loop**: `(*in)[j].DeepCopyInto(&(*out)[j])`, over the
element type's deep copy `hdc`. -/
theorem wp_slice_elem_deepcopy {V E : Type} [ZeroVal V] [TypedPointsto (GF := GF) V]
    (T : go.GoType) [IntoValTyped (GF := GF) V T]
    (inner : V → DFrac → E → IProp GF)
    (hdc : ∀ (a b : Loc) (x w : V) (dq : DFrac) (e : E),
      {{ (a ↦{dq} x : IProp GF) ∗ inner x dq e ∗ b ↦ w }}
        (App (Val (a @!! go.GoType.PointerType T @!! go!"DeepCopyInto")) (Val #b))
      {{ (y : V), RET #(); a ↦{dq} x ∗ inner x dq e ∗ b ↦ y ∗ inner y (DFrac.own 1) e }})
    (sl s' : GoSlice) (vs : List V) (ds : List E) (dq : DFrac) (n j : Nat) (x : V)
    (hx : vs[j]? = some x) (hjn : j < n) (hj64 : j < 2 ^ 63) :
    {{ (sl ↦*{dq} vs : IProp GF) ∗ ([∗list] x;e ∈ vs;ds, inner x dq e) ∗
        copyPrefix inner s' n ds j }}
      (App (Val (sliceIndexRef V (sint.Z (W64 (j : Int))) sl @!! go.GoType.PointerType T @!!
          go!"DeepCopyInto"))
        (Val #(sliceIndexRef V (sint.Z (W64 (j : Int))) s')))
    {{ RET #(); sl ↦*{dq} vs ∗ ([∗list] x;e ∈ vs;ds, inner x dq e) ∗
        copyPrefix inner s' n ds (j + 1) }} := by
  iintro %Φ ⟨Hs, Hl, Hc⟩ HΦ
  unfold copyPrefix
  icases Hc with ⟨%ys, Hs', Hy, %hys⟩
  have hjz : sint.Z (W64 (j : Int)) = j := by word
  have hjn' : (sint.Z (W64 (j : Int))).toNat = j := by rw [hjz]; simp
  ihave %hlen := BigSepL2.bigSepL2_length $$ Hl
  obtain ⟨e, he⟩ : ∃ e, ds[j]? = some e := by
    have := (List.getElem?_eq_some_iff.1 hx).1
    exact ⟨_, List.getElem?_eq_getElem (by omega)⟩
  icases BigSepL2.bigSepL2_lookup_acc hx he $$ Hl with ⟨Hx, Hl⟩
  icases ownSlice_elem_acc (sint.Z (W64 (j : Int))) x sl dq vs (by omega) (by rw [hjn']; exact hx)
    $$ Hs with ⟨Ha, Hs⟩
  have hz : (ys ++ (List.replicate n (zero_val V)).drop j)[(sint.Z (W64 (j : Int))).toNat]? =
      some (zero_val V) := by
    rw [hjn', List.getElem?_append_right (by omega)]
    simp only [hys, Nat.sub_self, List.getElem?_drop, Nat.add_zero, List.getElem?_replicate]
    simp [hjn]
  icases ownSlice_elem_acc (sint.Z (W64 (j : Int))) (zero_val V) s' (DFrac.own 1) _ (by omega) hz
    $$ Hs' with ⟨Hb, Hs'⟩
  iapply hdc $$ [Ha Hx Hb]
  · iframe
  inext
  iintro %y ⟨Ha, Hx, Hb, Hy'⟩
  ihave Hs := Hs $$ Ha
  ihave Hs' := Hs' $$ Hb
  ihave Hl := Hl $$ Hx
  iapply HΦ
  have hset : vs.set (sint.Z (W64 (j : Int))).toNat x = vs := by
    rw [hjn']; exact list_set_lookup_self vs j x hx
  have hset' : (ys ++ (List.replicate n (zero_val V)).drop j).set (sint.Z (W64 (j : Int))).toNat y =
      (ys ++ [y]) ++ (List.replicate n (zero_val V)).drop (j + 1) := by
    rw [hjn', List.set_append_right _ _ (by omega), hys, Nat.sub_self]
    have hd : (List.replicate n (zero_val V)).drop j =
        zero_val V :: (List.replicate n (zero_val V)).drop (j + 1) := by
      simp only [List.drop_replicate]
      have : n - j = (n - (j + 1)) + 1 := by omega
      rw [this, List.replicate_succ]
    rw [hd]
    simp
  have htake : ds.take (j + 1) = ds.take j ++ [e] := by
    rw [List.take_add_one, he]; rfl
  rw [hset, hset', htake]
  iframe
  isplitl
  · iapply (BigSepL2.bigSepL2_nil (PROP := IProp GF)).2; iempintro
  · ipureintro; simp [hys]

end lemmas

/-! ### `metav1.Time` (a basic deep value: `DeepCopyInto` is `*out = *t`, `time.go`) -/

section time
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apimachinery.pkg.apis.«meta».v1.Assumptions]

/-- `t.DeepCopyInto(out)` on a `*metav1.Time`: `*out = *t`. -/
theorem metav1Time.wp_DeepCopyInto (t o : Loc) (x w : k8s_io.apimachinery.pkg.apis.«meta».v1.Time)
    (dq : DFrac) :
    {{ (t ↦{dq} x : IProp GF) ∗ o ↦ w }}
      (App (Val (t @!! go.GoType.PointerType k8s_io.apimachinery.pkg.apis.«meta».v1.Time.ty @!! go!"DeepCopyInto")) (Val #o))
    {{ RET #(); t ↦{dq} x ∗ o ↦ x }} := by
  wp_start as ⟨Ht, Ho⟩
  wp_auto
  iapply HΦ
  iframe

/-- `t.DeepCopy()` on a non-nil `*metav1.Time`: a new `*Time` holding the same value. -/
theorem metav1Time.wp_DeepCopy (t : Loc) (x : k8s_io.apimachinery.pkg.apis.«meta».v1.Time)
    (dq : DFrac) :
    {{ (t ↦{dq} x : IProp GF) }}
      (App (Val (t @!! go.GoType.PointerType k8s_io.apimachinery.pkg.apis.«meta».v1.Time.ty @!! go!"DeepCopy")) (Val #()))
    {{ (t' : Loc), RET #t'; t ↦{dq} x ∗ t' ↦ x }} := by
  wp_start as Ht
  icases typedPointsto_not_null_dup _ _ _ $$ Ht with ⟨Ht, %Htnn⟩
  wp_auto
  wp_if_destruct
  · exact absurd rfl Htnn
  wp_apply metav1Time.wp_DeepCopyInto $$ [Ht «$r0»] as ⟨Ht, «$r0»⟩
  · iframe
  wp_auto
  iapply HΦ
  iframe

end time

end EtcdGrove
end Perennial

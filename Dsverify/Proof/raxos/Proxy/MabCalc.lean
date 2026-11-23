/-
Package `proxy`: leader mode 2's `hasAllDecided`, `updateEpochTime`, `calculateSequence`
(`proxymabhandler.go`).
-/
module

public import Dsverify.Proof.raxos.Proxy.MabSpecs
public import Dsverify.Proof.raxos.Hyp
public import Dsverify.Proof.raxos.LibDeps
public import Perennial.Proof.time.Link
public import Perennial.Proof.time.Results

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Perennial.raxos


open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open Perennial.raxos.pure Perennial.raxos.msg
open raxos.replica.src

instance mab_notInterface_int64 : go.NotInterface go.int64 := ⟨by unfold go.int64; trivial⟩

theorem mab_mul_small (x : w64) (m : Nat) (hm : m ≤ 5) (h0 : 0 ≤ sint.Z x) (h1 : sint.Z x ≤ 200000) :
    sint.Z (x * W64 (m : Int)) = sint.Z x * m := by
  have : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 := by omega
  rcases this with rfl|rfl|rfl|rfl|rfl|rfl <;> word

theorem mab_sdiv_small (x : w64) (m : Nat) (hm1 : 1 ≤ m) (hm : m ≤ 5) (h0 : 0 ≤ sint.Z x)
    (h1 : sint.Z x ≤ 100000) :
    sint.Z (BitVec.sdiv x (W64 (m : Int))) = (sint.Z x).tdiv m := by
  have hW : sint.Z (W64 (m : Int)) = m := by
    have : m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 := by omega
    rcases this with rfl|rfl|rfl|rfl|rfl <;> rfl
  rw [show sint.Z (BitVec.sdiv x (W64 (m : Int))) = (BitVec.sdiv x (W64 (m : Int))).toInt from rfl,
    BitVec.toInt_sdiv_of_ne_or_ne]
  · have hW' : (W64 (m : Int)).toInt = m := hW
    rw [hW']
  · right; intro h
    rw [h] at hW
    have : (-1#64 : w64).toInt = -1 := by decide
    have hW' : (-1#64 : w64).toInt = m := hW
    omega

/-- The value `epochTimes2[p-1]` that the greedy matching pairs with the sequence's entry `p`. -/
def mabF (b : List w64) (p : Nat) : w64 := b.getD (p - 1) 0

theorem mab_count_range (b : List w64) (v : w64) :
    b.count v = ((List.range b.length).filter (fun j => b.getD j 0 == v)).length := by
  induction b with
  | nil => simp
  | cons x b ih =>
    rw [List.length_cons, List.range_succ_eq_map, List.filter_cons, List.filter_map, List.count_cons, ih]
    have hf : ((fun j => (x :: b).getD j 0 == v) ∘ Nat.succ) = (fun j => b.getD j 0 == v) := by
      funext j; simp
    rw [hf]
    by_cases h : x = v <;> simp [h]

/-- The greedy matching never fails: a position `j` holding `a[i]` and not used yet exists. -/
theorem mab_greedy_exists (a b : List w64) (ps : List Nat) (i : Nat) (hab : a.Perm b)
    (hi : i < b.length) (hmap : ps.map (mabF b) = a.take i) :
    ∃ j, j < b.length ∧ b[j]? = a[i]? ∧ (j + 1) ∉ ps := by
  have hia : i < a.length := by rw [hab.length_eq]; exact hi
  let v := a[i]
  apply Classical.byContradiction
  intro hno
  have hall : ∀ j, j < b.length → b.getD j 0 = v → (j + 1) ∈ ps := by
    intro j hj hv
    apply Classical.byContradiction; intro hn
    apply hno; refine ⟨j, hj, ?_, hn⟩
    rw [List.getElem?_eq_getElem hia, List.getElem?_eq_getElem hj]
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj] at hv
    rw [hv]
  let J := (List.range b.length).filter (fun j => b.getD j 0 == v)
  have hJnd : J.Nodup := List.filter_sublist.nodup List.nodup_range
  let S := (ps.filter (fun p => mabF b p == v)).map (· - 1)
  have hJS : J ⊆ S := by
    intro j hj
    rw [List.mem_filter, List.mem_range] at hj
    have hv : b.getD j 0 = v := by simpa using hj.2
    have hp := hall j hj.1 hv
    rw [List.mem_map]
    refine ⟨j + 1, ?_, by simp⟩
    rw [List.mem_filter]
    refine ⟨hp, ?_⟩
    unfold mabF; rw [Nat.add_sub_cancel, hv]; simp
  have h1 : J.length ≤ S.length := hJnd.length_le_of_subset hJS
  have h2 : S.length = (ps.map (mabF b)).count v := by
    simp only [S, List.length_map, List.count_eq_length_filter, List.filter_map]
    congr 1
  have h3 : (a.take i).count v < (a.take (i + 1)).count v := by
    rw [List.take_add_one, List.getElem?_eq_getElem hia, List.count_append]
    simp [v]
  have h4 : (a.take (i + 1)).count v ≤ a.count v := (List.take_sublist _ _).count_le v
  have h5 : a.count v = b.count v := hab.count_eq v
  rw [hmap] at h2
  have h6 : b.count v = J.length := mab_count_range b v
  omega

/-- The greedy matching's step: the sequence extended by `j + 1`. -/
theorem mab_greedy_step (a b : List w64) (ps : List Nat) (i j : Nat) (n : Nat)
    (hb : b.length = n) (hj : j < n) (hv : b[j]? = a[i]?) (hia : i < a.length) (hn : (j + 1) ∉ ps)
    (hnd : ps.Nodup) (hr : ∀ p ∈ ps, 1 ≤ p ∧ p ≤ n) (hmap : ps.map (mabF b) = a.take i) :
    (ps ++ [j + 1]).Nodup ∧ (∀ p ∈ ps ++ [j + 1], 1 ≤ p ∧ p ≤ n) ∧
      (ps ++ [j + 1]).map (mabF b) = a.take (i + 1) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [List.nodup_append]
    refine ⟨hnd, by simp, ?_⟩
    intro x hx y hy; simp at hy; subst hy; intro h; subst h; exact hn hx
  · intro p hp
    rw [List.mem_append] at hp
    rcases hp with hp | hp
    · exact hr p hp
    · simp at hp; omega
  · rw [List.map_append, hmap, List.take_add_one]
    simp only [List.map_cons, List.map_nil]
    congr 1
    rw [List.getElem?_eq_getElem hia] at hv ⊢
    simp only [Option.toList_some, List.cons.injEq, and_true]
    simp [mabF, List.getD_eq_getElem?_getD, hv]

/-- `n` distinct values in `1..n`: a permutation of `1..n`. -/
theorem mab_perm_of_nodup (ps : List Nat) (n : Nat) (hnd : ps.Nodup)
    (hr : ∀ p ∈ ps, 1 ≤ p ∧ p ≤ n) (hl : ps.length = n) : isPerm n ps := by
  unfold isPerm
  rw [List.perm_iff_count]
  intro x
  rw [hnd.count, (List.nodup_range' (s := 1) (n := n)).count]
  by_cases hx : x ∈ List.range' 1 n
  · have hxp : x ∈ ps := by
      apply Classical.byContradiction; intro hxp
      have hsub : ps ⊆ (List.range' 1 n).erase x := by
        intro p hp
        have hpx : p ≠ x := fun h => hxp (h ▸ hp)
        rw [List.mem_erase_of_ne hpx, List.mem_range']
        have := hr p hp
        exact ⟨p - 1, by omega, by omega⟩
      have := hnd.length_le_of_subset hsub
      rw [List.length_erase_of_mem hx, List.length_range'] at this
      have : 1 ≤ n := by rw [List.mem_range'] at hx; omega
      omega
    simp [hx, hxp]
  · have hxp : x ∉ ps := by
      intro hxp; apply hx
      rw [List.mem_range']
      have := hr x hxp
      exact ⟨x - 1, by omega, by omega⟩
    simp [hx, hxp]

/-- A one-digit string (the lab's `digitString`). -/
def digitString (d : Int) : GoString := [W8 (48 + d)]

/-- `fmtInt i 10` of a digit `0 ≤ i < 10` (the main tree's `strconv.FormatInt.spec` gives
`fmtInt`): its one-digit string. -/
theorem fmtInt_digit (i : w64) (h0 : 0 ≤ sint.Z i) (h10 : sint.Z i < 10) :
    internal.strconv.fmtInt i (W64 10) = digitString (sint.Z i) := by
  obtain ⟨n, hn, rfl⟩ : ∃ n : Nat, n < 10 ∧ i = W64 (n : Int) := ⟨(sint.Z i).toNat, by omega, by word⟩
  have : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 ∨ n = 9 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  · unfold internal.strconv.fmtInt internal.strconv.fmtUint
    rw [if_neg (by decide), dif_pos (by decide), internal.strconv.baseDigits, if_pos (by decide)]
    decide

/-- `decimal` of a replica `1..5`: `FormatInt`'s one-digit string. -/
theorem mab_decimal_digit (p : Nat) (h1 : 1 ≤ p) (h5 : p ≤ 5) : decimal p = digitString p := by
  have : p = 1 ∨ p = 2 ∨ p = 3 ∨ p = 4 ∨ p = 5 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl <;>
  · simp only [decimal, digitString, Nat.toString_eq_ofList_toDigits, String.toUTF8_eq_toByteArray,
      String.toByteArray_ofList]
    rw [Nat.toDigits_of_lt_base (by omega)]
    simp only [Nat.digitChar_eq_one.2 rfl, Nat.digitChar_eq_two.2 rfl, Nat.digitChar_eq_three.2 rfl, Nat.digitChar_eq_four.2 rfl, Nat.digitChar_eq_five.2 rfl]
    decide +kernel

/-- `calculateSequence`'s string `s` after the entries `ps`: `",p"` for each. -/
def mabAcc (ps : List Nat) : GoString := (ps.map (fun p => go!"," ++ decimal p)).flatten

theorem mabAcc_snoc (ps : List Nat) (p : Nat) :
    mabAcc (ps ++ [p]) = mabAcc ps ++ go!"," ++ decimal p := by
  simp [mabAcc]

theorem mabAcc_length (ps : List Nat) (hr : ∀ p ∈ ps, 1 ≤ p ∧ p ≤ 5) :
    (mabAcc ps).length = 2 * ps.length := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    have h1 := ih (fun q hq => hr q (List.mem_cons_of_mem _ hq))
    unfold mabAcc at h1 ⊢
    rw [List.map_cons, List.flatten_cons, List.length_append, h1, List.length_append,
      mab_decimal_digit p (hr p (by simp)).1 (hr p (by simp)).2]
    simp [digitString]; omega

theorem mab_intersperse (sep : GoString) (y : GoString) (ys : List GoString) :
    (List.intersperse sep (y :: ys)).flatten = y ++ (ys.map (sep ++ ·)).flatten := by
  induction ys generalizing y with
  | nil => simp
  | cons z zs ih => rw [List.intersperse_cons_cons, List.flatten_cons, List.flatten_cons, ih]; simp

theorem mabAcc_drop (ps : List Nat) (h : ps ≠ []) : (mabAcc ps).drop 1 = seqStr ps := by
  cases ps with
  | nil => exact absurd rfl h
  | cons x xs =>
    unfold seqStr mabAcc
    rw [List.map_cons, List.map_cons, mab_intersperse]
    simp [List.map_map, Function.comp_def]

section proofs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [π : NetProtoGS] [qv : hyp.QpVocab GF]
variable [raxos.replica.src.Assumptions] [raxos.proto.client.Assumptions]
variable [strconv.Assumptions] [time.Assumptions] [hsort : hyp.SortHyp GF]
variable [QpFormatIntDeps GF]

/-- `strconv.FormatInt(i, 10)` for `0 <= i < 10` (the lab's `strconv.wp_FormatInt`), from the
main tree's `strconv.FormatInt.spec`. -/
theorem wp_FormatInt_digit (i : w64) (h0 : 0 ≤ sint.Z i) (h10 : sint.Z i < 10) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.strconv }}
      (App (App (Val (@! _root_.Perennial.strconv.FormatInt)) (Val #i)) (Val #(W64 10)))
    {{ RET #(digitString (sint.Z i)); True }} := by
  iintro %Φ #Hpkg HΦ
  iapply (QpFormatIntDeps.formatInt i (W64 10))
  · iframe Hpkg; ipureintro; decide
  inext
  iintro %str %Hstr
  rw [Hstr, fmtInt_digit i h0 h10]
  iapply HΦ
  itrivial

attribute [local instance] HeapGS.goose_globalGS

theorem wp_hasAllDecided : hasAllDecided_spec (GF := GF) (hG := hG) := by
  intro c k pr e rl slots
  wp_start as ⟨#Hc, %Hok, Hrl, Hsl⟩
  iunfold sharedConsts at Hc
  icases Hc with ⟨-, -, -, -, -, -, #Hep, #Hn⟩
  wp_auto
  obtain ⟨Hcok, He0, He1⟩ := Hok
  have Hep1 : 1 ≤ c.ep ∧ c.ep ≤ 5 := ⟨Hcok.2.2.2.2.1, Hcok.2.2.2.2.2.1⟩
  have Hs0 : sint.Z (e * W64 c.ep) = sint.Z e * c.ep := mab_mul_small e c.ep Hep1.2 He0 (by omega)
  have Hs1' := mab_mul_small (e + W64 1) c.ep Hep1.2 (by word) (by word)
  rw [show sint.Z (e + W64 1) = sint.Z e + 1 by word, Int.add_mul, Int.one_mul] at Hs1'
  have HP : sint.Z e * c.ep ≤ 500000 := by
    have := Int.mul_le_mul (a := sint.Z e) (b := (c.ep : Int)) (c := 100000) (d := 5) (by omega) (by omega) (by omega) (by omega)
    omega
  have HP0 : 0 ≤ sint.Z e * c.ep := Int.mul_nonneg He0 (by omega)
  generalize sint.Z e * c.ep = P at Hs0 Hs1' HP HP0
  have Hs1 : sint.Z ((e + W64 1) * W64 c.ep - W64 2) = P + c.ep - 2 := by
    generalize (e + W64 1) * W64 c.ep = x at Hs1' ⊢
    word
  ihave HI : (∃ (j : w64), "i" ∷ i_ptr ↦ j ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ P + c.ep - 1⌝ : IProp GF) $$ [i]
  · iexists _; iframe; ipureintro; omega
  wp_for HI
  rw [Hs1]
  ihave %Hrllen := ownSlice_len $$ Hsl
  wp_if_destruct
  · wp_if_destruct
    · have Hilt : sint.nat j < slots.length := by word
      list_elem slots (sint.nat j) as s
      have Hb : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z rl.len := ⟨Hj.1, by word⟩
      icases ownSlice_elem_acc (sint.Z j) s rl _ slots Hb.1 (by simpa using Hs_lookup) $$ Hsl
        with ⟨Hel, Hsl⟩
      repeat' (first | wp_auto | simp only [Hb, _root_.and_self, ↓reduceIte])
      ihave Hsl := Hsl $$ Hel
      rw [list_set_lookup_self _ _ _ (by simpa using Hs_lookup)]
      wp_if_destruct
      · wp_for_post
        iframe
        iexists _; iframe; ipureintro; word
      · wp_for_post
        iapply HΦ; iframe
    · wp_for_post
      iapply HΦ; iframe
  · iapply HΦ; iframe

theorem wp_updateEpochTime (wp_hasAllDecided : hasAllDecided_spec (GF := GF) (hG := hG)) :
    updateEpochTime_spec (GF := GF) (hG := hG) := by
  intro c k pr i rl slots
  wp_start as ⟨#Hc, %Hok, Hep, Hrl, Hsl⟩
  ihave #Hc2 := Hc
  iunfold sharedConsts at Hc2
  icases Hc2 with ⟨-, -, -, -, #Hlm, -, #Hepz, #Hn⟩
  iunfold epochOwn at Hep
  icases Hep with ⟨%et, %ets, Het, Hets, Hetc⟩
  wp_auto
  obtain ⟨Hcok, Hi0, Hi1⟩ := Hok
  have Hep1 : 1 ≤ c.ep ∧ c.ep ≤ 5 := ⟨Hcok.2.2.2.2.1, Hcok.2.2.2.2.2.1⟩
  have Hne : sint.Z (W64 (c.ep : Int)) ≠ 0 := by word
  have Hdiv : 0 ≤ sint.Z (BitVec.sdiv i (W64 (c.ep : Int))) ∧ sint.Z (BitVec.sdiv i (W64 (c.ep : Int))) ≤ 100000 := by
    rw [mab_sdiv_small i c.ep Hep1.1 Hep1.2 Hi0 Hi1]
    constructor
    · exact Int.tdiv_nonneg Hi0 (by omega)
    · have := Int.tdiv_le_self (c.ep : Int) Hi0
      omega
  simp only [Hne, ↓reduceIte]
  generalize BitVec.sdiv i (W64 (c.ep : Int)) = ep at Hdiv
  wp_auto
  ihave HI : (∃ (et : GoSlice) (ets : List EpochTime), "Het" ∷ pr.[Proxy, go!"epochTimes"] ↦ et ∗
      "Hets" ∷ et ↦* ets ∗ "Hetc" ∷ ownSliceCap EpochTime et (DFrac.own 1) : IProp GF) $$ [Het Hets Hetc]
  · iexists et, ets; iframe
  wp_for HI
  wp_if_destruct
  · wp_bind (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType EpochTime.ty))))
      (Val (LiteralValueV _)))
    iapply wp_slice_literal (V := EpochTime) (t := EpochTime.ty) [EpochTime.mk (zero_val time.Time) (zero_val time.Time) false false]
    wp_auto
    isplitl []
    · ipureintro; rfl
    iintro %lit_ptr ⟨Hlit, -⟩
    wp_apply wp_slice_append (V := EpochTime) _ _ _ _ _ $$ [$Hets $Hetc $Hlit] as %et' ⟨Hets, Hetc, -⟩
    wp_for_post
    iframe
    iexists et', _; iframe
  ihave %Hetlen := ownSlice_len $$ Hets
  have Hb : 0 ≤ sint.Z ep ∧ sint.Z ep < sint.Z et.len := ⟨Hdiv.1, by word⟩
  have Hilt : sint.nat ep < ets.length := by word
  list_elem ets (sint.nat ep) as s
  icases ownSlice_elem_acc (sint.Z ep) s et _ ets Hb.1 (by simpa using Hs_lookup) $$ Hets
    with ⟨Hel, Hets⟩
  repeat' (first | wp_auto | simp only [Hb, _root_.and_self, ↓reduceIte])
  wp_join iprop(∃ s' : EpochTime, "Hel" ∷ sliceIndexRef EpochTime (sint.Z ep) et ↦ s' ∗
      "Het" ∷ pr.[Proxy, go!"epochTimes"] ↦ et ∗ "pr" ∷ pr_ptr ↦ pr ∗ "epoch" ∷ epoch_ptr ↦ ep) with [Hel Het pr epoch]
    as ⟨%s1, Hel, Het, pr, epoch⟩
  · repeat' (first | wp_auto | simp only [Hb, _root_.and_self, ↓reduceIte])
    wp_apply time.wp_Now as %t -
    repeat' (first | wp_auto | simp only [Hb, _root_.and_self, ↓reduceIte])
    isplitl []
    · itrivial
    iexists _; iframe
  rcases s1 with ⟨st1, et1, sd1, ed1⟩
  cases ed1
  · repeat' (first | wp_auto | simp only [Hb, _root_.and_self, ↓reduceIte])
    wp_apply wp_hasAllDecided c k pr ep rl slots $$ [$Hrl $Hsl] as %b ⟨Hrl, Hsl⟩
    · iframe #; ipureintro; exact ⟨Hcok, Hdiv⟩
    cases b
    · wp_auto
      ihave Hets := Hets $$ Hel
      iapply HΦ; iframe
      iunfold epochOwn; iexists et, _; iframe
    · repeat' (first | wp_auto | simp only [Hb, _root_.and_self, ↓reduceIte])
      wp_apply time.wp_Now as %t -
      repeat' (first | wp_auto | simp only [Hb, _root_.and_self, ↓reduceIte])
      ihave Hets := Hets $$ Hel
      iapply HΦ; iframe
      iunfold epochOwn; iexists et, _; iframe
  · repeat' (first | wp_auto | simp only [Hb, _root_.and_self, ↓reduceIte])
    ihave Hets := Hets $$ Hel
    iapply HΦ; iframe
    iunfold epochOwn; iexists et, _; iframe

/-- `pr.notInarray(sequence, i)`: whether `i` is not in `sequence`. -/
theorem wp_notInarray (pr : Loc) (sl : GoSlice) (xs : List w64) (x : w64) :
    {{ (sl ↦* xs : IProp GF) }}
      (App (App (Val (pr @!! go.GoType.PointerType Proxy.ty @!! go!"notInarray")) (Val #sl)) (Val #x))
    {{ RET #(decide (x ∉ xs)); sl ↦* xs }} := by
  wp_start as Hsl
  wp_auto
  ihave %Hlen := ownSlice_len $$ Hsl
  ihave HI : (∃ (j : w64), "j" ∷ j_ptr ↦ j ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z sl.len ∧ ∀ m : Nat, m < sint.nat j → xs[m]? ≠ some x⌝ : IProp GF) $$ [j]
  · iexists W64 0; iframe; ipureintro; refine ⟨by word, by word, fun m hm => ?_⟩; exact absurd hm (by word)
  wp_for HI
  wp_if_destruct
  · have Hjl : sint.Z j < sint.Z sl.len := by simpa using Hif
    have Hjn : sint.nat j < xs.length := by word
    list_elem xs (sint.nat j) as y
    have Hb : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z sl.len := ⟨Hj.1, Hjl⟩
    repeat' (first | wp_auto | simp only [Hb, _root_.and_self, ↓reduceIte])
    wp_apply wp_load_slice_index sl (sint.Z j) xs _ y Hj.1 $$ [Hsl] as Hsl
    · iframe Hsl; ipureintro; rw [show (sint.Z j).toNat = sint.nat j by word]; exact Hy_lookup
    wp_if_destruct
    · wp_for_post
      have : x ∈ xs := by rw [← Hif]; exact List.mem_of_getElem? Hy_lookup
      rw [decide_eq_false (fun h => h this)]
      iapply HΦ; iframe
    · wp_for_post
      iframe
      iexists j + W64 1; iframe; ipureintro
      refine ⟨by word, by word, fun m hm => ?_⟩
      by_cases hmj : m = sint.nat j
      · subst hmj; rw [Hy_lookup]; intro h; cases h; exact Hif rfl
      · exact Hj.2.2 m (by word)
  · have Hjl : sint.Z j = sint.Z sl.len := by
      have : ¬ sint.Z j < sint.Z sl.len := by simpa using Hif
      omega
    have : x ∉ xs := by
      intro hx
      obtain ⟨m, hm, hmx⟩ := List.getElem_of_mem hx
      exact Hj.2.2 m (by word) (by simp [hm, hmx])
    rw [decide_eq_true this]
    iapply HΦ; iframe

theorem mab_set_replicate {α : Type} (l : List α) (z x : α) (n : Nat) (h : l.length < n) :
    (l ++ List.replicate (n - l.length) z).set l.length x =
      (l ++ [x]) ++ List.replicate (n - (l ++ [x]).length) z := by
  rw [List.set_append_right _ _ (by omega), Nat.sub_self]
  obtain ⟨m, hm⟩ : ∃ m, n - l.length = m + 1 := ⟨n - l.length - 1, by omega⟩
  rw [hm, List.replicate_succ, List.set_cons_zero, List.length_append, List.length_singleton,
    show n - (l.length + 1) = m by omega, List.append_assoc]
  rfl

theorem mab_w64_succ (jj : w64) (h0 : 0 ≤ sint.Z jj) (h1 : sint.Z jj < 5) :
    W64 (((sint.nat jj + 1 : Nat)) : Int) = jj + W64 1 := by
  have : sint.Z jj = 0 ∨ sint.Z jj = 1 ∨ sint.Z jj = 2 ∨ sint.Z jj = 3 ∨ sint.Z jj = 4 := by omega
  rcases this with h | h | h | h | h <;>
  · have hn : sint.nat jj = (sint.Z jj).toNat := rfl
    rw [hn, h]; word

theorem mab_seqOf_snoc (ps : List Nat) (jj : w64) (h0 : 0 ≤ sint.Z jj) (h1 : sint.Z jj < 5) :
    seqOf ps ++ [jj + W64 1] = seqOf (ps ++ [sint.nat jj + 1]) := by
  rw [← mab_w64_succ jj h0 h1]
  unfold seqOf
  rw [List.map_append, List.map_singleton]

theorem mab_seqOf_mem (ps : List Nat) (hr : ∀ p ∈ ps, 1 ≤ p ∧ p ≤ 5) (jj : w64)
    (h0 : 0 ≤ sint.Z jj) (h1 : sint.Z jj < 5) :
    (jj + W64 1) ∈ seqOf ps ↔ (sint.nat jj + 1) ∈ ps := by
  rw [← mab_w64_succ jj h0 h1]
  unfold seqOf
  rw [List.mem_map]
  constructor
  · rintro ⟨p, hp, hpe⟩
    have hp5 := hr p hp
    have : p = sint.nat jj + 1 := by
      have hn : sint.nat jj = (sint.Z jj).toNat := rfl
      have h2 : sint.Z (W64 (p : Int)) = p := by word
      have h3 : sint.Z (W64 ((sint.nat jj + 1 : Nat) : Int)) = sint.nat jj + 1 := by rw [hn]; word
      rw [hpe] at h2; omega
    subst this; exact hp
  · intro h; exact ⟨_, h, rfl⟩
/-- `calculateSequence`'s `times`: each replica's measured epoch times (any values), owned. -/
def mabTimesOwn (tss : List GoSlice) : IProp GF :=
  iprop([∗list] t ∈ tss, ∃ xs : List w64, t ↦* xs ∗ ownSliceCap w64 t (DFrac.own 1))

theorem mabTimesOwn_snoc (tss : List GoSlice) (t : GoSlice) (xs : List w64) :
    mabTimesOwn (GF := GF) tss ∗ t ↦* xs ∗ ownSliceCap w64 t (DFrac.own 1) ⊢ mabTimesOwn (tss ++ [t]) := by
  iintro ⟨Hts, Ht, Htc⟩
  iunfold mabTimesOwn at Hts
  iunfold mabTimesOwn
  iapply BigSepL.bigSepL_snoc.2
  iframe Hts
  iexists xs; iframe

set_option maxHeartbeats 2000000 in
theorem wp_calculateSequence (wp_getLeaderSequence : getLeaderSequence_spec (GF := GF) (hG := hG)) :
    calculateSequence_spec (GF := GF) (hG := hG) := by
  intro γ γs c k pr e rl slots L
  wp_start as ⟨#Hc, %Hok, #Hinv, #Hconf, Hlog, Hep⟩
  ihave #Hc2 := Hc
  iunfold sharedConsts at Hc2
  icases Hc2 with ⟨-, -, -, -, #Hlm, -, #Hepz, #Hn⟩
  iunfold epochOwn at Hep
  icases Hep with ⟨%et, %ets, Het, Hets, Hetc⟩
  wp_auto
  obtain ⟨Hcok, Hk1, Hk2, He0, He1⟩ := Hok
  have Hn35 : c.n = 3 ∨ c.n = 5 := Hcok.1
  have Hep1 : 1 ≤ c.ep ∧ c.ep ≤ 5 := ⟨Hcok.2.2.2.2.1, Hcok.2.2.2.2.2.1⟩
  have H2n : sint.Z (W64 2 * W64 (c.n : Int)) = 2 * c.n := by
    rw [mab_mul_small (W64 2) c.n (by omega) (by decide) (by decide)]; rfl
  rw [H2n, decide_eq_false (by omega)]
  wp_auto
  have Hnz : sint.Z (W64 (c.n : Int)) = c.n := by rcases Hn35 with h | h <;> rw [h] <;> rfl
  wp_apply (wp_slice_make2 (V := GoSlice)) as %tm ⟨Htm, Htmc⟩
  · ipureintro; omega
  -- `times[i] = make([]int64, 0)` for each replica
  ihave HI : (∃ (j : w64) (tss : List GoSlice), "i" ∷ i_ptr ↦ j ∗
      "Htm" ∷ tm ↦* (tss ++ List.replicate (c.n - tss.length) (zero_val GoSlice)) ∗
      "Hts" ∷ mabTimesOwn tss ∗ "%Hj" ∷ ⌜sint.Z j = tss.length ∧ tss.length ≤ c.n⌝ : IProp GF)
      $$ [i Htm]
  · iexists W64 0, []
    rw [show sint.nat (W64 (c.n : Int)) = c.n - ([] : List GoSlice).length by
      rcases Hn35 with h | h <;> rw [h] <;> rfl]
    iframe
    isplitl []
    · iunfold mabTimesOwn; iapply BigSepL.bigSepL_nil.2; iempintro
    ipureintro; simp
  wp_for HI
  wp_if_destruct
  · have Hlt : tss.length < c.n := by rw [Hnz] at Hif; omega
    wp_apply (wp_slice_make2 (V := w64)) as %t0 ⟨Ht0, Ht0c⟩
    · ipureintro; word
    ihave %Htmlen := ownSlice_len $$ Htm
    simp only [List.length_append, List.length_replicate] at Htmlen
    have Hb : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z tm.len := ⟨by omega, by have := Htmlen.1; word⟩
    repeat' (first | wp_auto | simp only [Hb, _root_.and_self, ↓reduceIte])
    wp_apply wp_store_slice_index $$ [Htm] as Htm
    · iframe Htm; ipureintro; simp only [List.length_append, List.length_replicate]; omega
    rw [show (sint.Z j).toNat = tss.length by omega, mab_set_replicate _ _ _ _ Hlt]
    wp_for_post
    iframe
    iexists j + W64 1, tss ++ [t0]
    iframe
    isplitl [Ht0 Ht0c Hts]
    · iapply mabTimesOwn_snoc $$ [$Hts $Ht0 $Ht0c]
    ipureintro; simp only [List.length_append, List.length_singleton]; constructor <;> word
  have Htl : tss.length = c.n := by rw [Hnz] at Hif; omega
  rw [Htl, Nat.sub_self, List.replicate_zero, List.append_nil]
  -- the tracked epochs' times, by their leaders
  ihave %Hetlen := ownSlice_len $$ Hets
  wp_join iprop(∃ (j : w64) (tss : List GoSlice), "i" ∷ i_ptr ↦ j ∗
      "Htm" ∷ tm ↦* tss ∗ "Hts" ∷ mabTimesOwn tss ∗ "Hlog" ∷ logRd γ γs c pr rl slots L ∗
      "Het" ∷ pr.[Proxy, go!"epochTimes"] ↦ et ∗ "Hets" ∷ et ↦* ets ∗ "pr" ∷ pr_ptr ↦ pr ∗
      "epoch" ∷ epoch_ptr ↦ e ∗ "times" ∷ times_ptr ↦ tm ∗ "%Htl" ∷ ⌜tss.length = c.n⌝)
      at next with [i Htm Hts Hlog Het Hets pr epoch times] as ⟨%j0, %tss, i, Htm, Hts, Hlog, Het, Hets, pr, epoch, times, %Htl⟩
  · ihave HI : (∃ (j : w64) (tss : List GoSlice), "i" ∷ i_ptr ↦ j ∗
        "Htm" ∷ tm ↦* tss ∗ "Hts" ∷ mabTimesOwn tss ∗ "Hlog" ∷ logRd γ γs c pr rl slots L ∗
        "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z e ∧ tss.length = c.n⌝ : IProp GF)
        $$ [i Htm Hts Hlog]
    · iexists W64 0, tss; iframe; ipureintro
      exact ⟨by word, by rw [show sint.Z (W64 0) = 0 from rfl]; omega, Htl⟩
    wp_for HI
    wp_if_destruct
    · wp_if_destruct
      · have Hb : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z et.len := ⟨Hj.1, Hif⟩
        have Hilt : sint.nat j < ets.length := by word
        list_elem ets (sint.nat j) as s
        icases ownSlice_elem_acc (sint.Z j) s et _ ets Hb.1 (by simpa using Hs_lookup) $$ Hets
          with ⟨Hel, Hets⟩
        repeat' (first | wp_auto | simp only [Hb, _root_.and_self, ↓reduceIte])
        wp_if_destruct
        · have Hje : sint.Z (j * W64 (c.ep : Int)) = sint.Z j * c.ep :=
            mab_mul_small j c.ep Hep1.2 Hj.1 (by omega)
          have Hjb : 0 ≤ sint.Z j * c.ep ∧ sint.Z j * c.ep ≤ 100000 := by
            refine ⟨Int.mul_nonneg Hj.1 (by omega), ?_⟩
            have := Int.mul_le_mul (a := sint.Z j) (b := (c.ep : Int)) (c := 1000) (d := 5)
              (by omega) (by omega) (by omega) (by omega)
            omega
          wp_apply wp_getLeaderSequence γ γs c k pr (j * W64 (c.ep : Int)) rl slots L $$ [Hlog]
            as %qs %q ⟨Hqs, %Hq, -, Hlog⟩
          · iframe #; iframe; ipureintro; refine ⟨Hcok, Hk1, Hk2, ?_, ?_⟩ <;> omega
          ihave %Hqlen := ownSlice_len $$ Hqs
          have Hql : q.length = c.n := by unfold isPerm at Hq; rw [Hq.length_eq, List.length_range']
          obtain ⟨ld, hld⟩ : ∃ ld, q[0]? = some ld := ⟨q[0], List.getElem?_eq_getElem (by omega)⟩
          have Hld : 1 ≤ ld ∧ ld ≤ c.n := by
            have hm : ld ∈ List.range' 1 c.n := Hq.mem_iff.1 (List.mem_of_getElem? hld)
            rw [List.mem_range'] at hm; omega
          have Hb0 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z qs.len := by
            simp only [seqOf, List.length_map] at Hqlen; constructor <;> word
          repeat' (first | wp_auto | simp only [Hb0, _root_.and_self, ↓reduceIte])
          wp_apply wp_load_slice_index qs (sint.Z (W64 0)) (seqOf q) _ (W64 (ld : Int)) Hb0.1 $$ [Hqs]
            as Hqs
          · iframe Hqs; ipureintro; simp [seqOf, hld]
          ihave %Htmlen := ownSlice_len $$ Htm
          have Hb1 : 0 ≤ sint.Z (W64 (ld : Int) - W64 1) ∧ sint.Z (W64 (ld : Int) - W64 1) < sint.Z tm.len := by
            have hl5 : ld = 1 ∨ ld = 2 ∨ ld = 3 ∨ ld = 4 ∨ ld = 5 := by omega
            have := Htmlen.1
            rcases hl5 with h | h | h | h | h <;> subst h <;> constructor <;> word
          have Hld1 : sint.nat (W64 (ld : Int) - W64 1) = ld - 1 := by
            have : ld = 1 ∨ ld = 2 ∨ ld = 3 ∨ ld = 4 ∨ ld = 5 := by omega
            rcases this with h | h | h | h | h <;> subst h <;> rfl
          repeat' (first | wp_auto | simp only [Hb1, Hb, _root_.and_self, ↓reduceIte])
          have Htn : ld - 1 < tss.length := by omega
          list_elem tss (ld - 1) as t
          wp_apply wp_load_slice_index tm _ tss _ t Hb1.1 $$ [Htm] as Htm
          · iframe Htm; ipureintro; rw [show (sint.Z (W64 (ld : Int) - W64 1)).toNat = ld - 1 from Hld1]
            exact Ht_lookup
          iunfold mabTimesOwn at Hts
          icases BigSepL.bigSepL_insert_acc Ht_lookup $$ Hts with ⟨⟨%xs, Ht, Htc⟩, Hts⟩
          repeat' (first | wp_auto | simp only [Hb1, Hb, _root_.and_self, ↓reduceIte])
          icases (Access.access (PROP := IProp GF)
            (A := iprop((sliceIndexRef EpochTime (sint.Z j) et).[EpochTime, go!"endTime"] ↦ s.endTime'))
            (A' := iprop((sliceIndexRef EpochTime (sint.Z j) et).[EpochTime, go!"endTime"] ↦ s.endTime'))
            (P := iprop(sliceIndexRef EpochTime (sint.Z j) et ↦ s))) $$ Hel with ⟨Hf, Hback⟩
          wp_apply time.Time.wp_ptr_Sub _ s.endTime' s.startTime' $$ [Hf] as %d Hf
          · iexact Hf
          ihave Hel := Hback $$ Hf
          wp_apply (time.Duration.wp_Microseconds d)
          wp_bind (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType go.int64))))
            (Val (LiteralValueV _)))
          iapply wp_slice_literal (V := w64) (t := go.int64) [BitVec.sdiv d (W64 1000)]
          wp_auto
          isplitl []
          · ipureintro; rfl
          iintro %lit_ptr ⟨Hlit, -⟩
          wp_apply wp_slice_append (V := w64) _ _ _ _ _ $$ [$Ht $Htc $Hlit] as %t' ⟨Ht, Htc, -⟩
          repeat' (first | wp_auto | simp only [Hb1, Hb, _root_.and_self, ↓reduceIte])
          wp_apply wp_store_slice_index $$ [Htm] as Htm
          · iframe Htm; ipureintro; exact ⟨Hb1.1, by have := Htmlen.1; word⟩
          ihave Hts := Hts $$ [Ht Htc]
          · iexists _; iframe
          ihave Hets := Hets $$ Hel
          rw [show ets.set (sint.Z j).toNat s = ets from list_set_lookup_self _ _ _ (by simpa using Hs_lookup),
            show (sint.Z (W64 (ld : Int) - W64 1)).toNat = ld - 1 from Hld1]
          wp_for_post
          iframe
          iexists j + W64 1, _
          iframe
          iunfold mabTimesOwn
          iframe
          ipureintro
          refine ⟨by word, by word, by simp [Hj.2.2]⟩
        · wp_for_post
          ihave Hets := Hets $$ Hel
          rw [list_set_lookup_self _ _ _ (by simpa using Hs_lookup)]
          isplitl []
          · itrivial
          iexists j, tss; iframe; ipureintro; exact Hj.2.2
      · isplitl []
        · itrivial
        iexists j, tss; iframe; ipureintro; exact Hj.2.2
    · isplitl []
      · itrivial
      iexists j, tss; iframe; ipureintro; exact Hj.2.2
  -- the averages
  wp_apply (wp_slice_make2 (V := w64)) as %e1 ⟨He1s, He1c⟩
  · ipureintro; word
  wp_apply (wp_slice_make2 (V := w64)) as %e2 ⟨He2s, He2c⟩
  · ipureintro; word
  have Hnn : sint.nat (W64 (c.n : Int)) = c.n := by rcases Hn35 with h | h <;> rw [h] <;> rfl
  rw [Hnn]
  ihave HI : (∃ (i : w64) (vs : List w64), "i" ∷ i_ptr ↦ i ∗
      "He1s" ∷ e1 ↦* (vs ++ List.replicate (c.n - vs.length) (W64 0)) ∗
      "He2s" ∷ e2 ↦* (vs ++ List.replicate (c.n - vs.length) (W64 0)) ∗
      "%Hi" ∷ ⌜sint.Z i = vs.length ∧ vs.length ≤ c.n⌝ : IProp GF) $$ [i He1s He2s]
  · iexists W64 0, []; iframe; ipureintro; simp
  wp_for HI
  wp_if_destruct
  · have Hil : vs.length < c.n := by rw [Hnz] at Hif; omega
    have Hti : sint.nat i < tss.length := by word
    list_elem tss (sint.nat i) as t
    ihave %Htmlen := ownSlice_len $$ Htm
    have Hbi : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z tm.len := ⟨by omega, by have := Htmlen.1; word⟩
    iunfold mabTimesOwn at Hts
    icases BigSepL.bigSepL_insert_acc Ht_lookup $$ Hts with ⟨⟨%xs, Ht, Htc⟩, Hts⟩
    ihave %Htlen := ownSlice_len $$ Ht
    ihave HJ : (∃ (jj sm cnt : w64), "j" ∷ j_ptr ↦ jj ∗ "sum" ∷ sum_ptr ↦ sm ∗ "count" ∷ count_ptr ↦ cnt ∗
        "%Hjj" ∷ ⌜0 ≤ sint.Z jj ∧ sint.Z jj ≤ sint.Z t.len⌝ : IProp GF) $$ [j sum count]
    · iexists W64 0, W64 0, W64 0; iframe; ipureintro; constructor <;> word
    have Hti' : tss[(sint.Z i).toNat]? = some t := by simpa using Ht_lookup
    wp_for HJ
    simp only [Hbi, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index tm (sint.Z i) tss _ t Hbi.1 $$ [Htm] as Htm
    · iframe Htm; ipureintro; exact Hti'
    wp_if_destruct
    · have Hjt : sint.Z jj < sint.Z t.len := by simpa [intoVal_eq_iff] using Hif
      have Hjl : sint.nat jj < xs.length := by word
      list_elem xs (sint.nat jj) as x
      have Hbj : 0 ≤ sint.Z jj ∧ sint.Z jj < sint.Z t.len := ⟨Hjj.1, Hjt⟩
      repeat' (first | wp_auto | simp only [Hbi, _root_.and_self, ↓reduceIte])
      wp_apply wp_load_slice_index tm (sint.Z i) tss _ t Hbi.1 $$ [Htm] as Htm
      · iframe Htm; ipureintro; exact Hti'
      repeat' (first | wp_auto | simp only [Hbj, _root_.and_self, ↓reduceIte])
      wp_apply wp_load_slice_index t (sint.Z jj) xs _ x Hbj.1 $$ [Ht] as Ht
      · iframe Ht; ipureintro; rw [show (sint.Z jj).toNat = sint.nat jj from rfl]; exact Hx_lookup
      wp_for_post
      iframe
      iexists jj + W64 1, _, _; iframe; ipureintro; constructor <;> word
    have Hjt : ¬ sint.Z jj < sint.Z t.len := by simpa [intoVal_eq_iff] using Hif
    rw [if_neg (by simpa using Hjt)]
    wp_auto
    wp_join iprop(∃ a : w64, "avg" ∷ avg_ptr ↦ a ∗ "sum" ∷ sum_ptr ↦ sm ∗ "count" ∷ count_ptr ↦ cnt)
      with [avg sum count] as ⟨%a, avg, sum, count⟩
    · have Hc0 : sint.Z cnt ≠ 0 := by
        have : sint.Z (W64 0) < sint.Z cnt := by simpa using Hif
        have h0 : sint.Z (W64 0) = 0 := rfl
        omega
      simp only [Hc0, ↓reduceIte]
      wp_auto
      isplitl []
      · ipureintro; rfl
      iexists _; iframe
    ihave %He1len := ownSlice_len $$ He1s
    ihave %He2len := ownSlice_len $$ He2s
    simp only [List.length_append, List.length_replicate] at He1len He2len
    have Hbe1 : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z e1.len := ⟨by omega, by have := He1len.1; word⟩
    have Hbe2 : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z e2.len := ⟨by omega, by have := He2len.1; word⟩
    have Hiv : (sint.Z i).toNat = vs.length := by omega
    simp only [Hbe1, _root_.and_self, ↓reduceIte]
    wp_apply wp_store_slice_index $$ [He1s] as He1s
    · iframe He1s; ipureintro; simp only [List.length_append, List.length_replicate]; omega
    repeat' (first | wp_auto | simp only [Hbe2, _root_.and_self, ↓reduceIte])
    wp_apply wp_store_slice_index $$ [He2s] as He2s
    · iframe He2s; ipureintro; simp only [List.length_append, List.length_replicate]; omega
    rw [Hiv, mab_set_replicate _ _ _ _ Hil]
    ihave Hts := Hts $$ [Ht Htc]
    · iexists _; iframe
    rw [list_set_lookup_self _ _ _ Ht_lookup]
    ihave Hts : mabTimesOwn (GF := GF) tss $$ [Hts]
    · iunfold mabTimesOwn; iexact Hts
    wp_for_post
    iframe
    iexists i + W64 1, vs ++ [a]
    iframe
    ipureintro; simp only [List.length_append, List.length_singleton]; constructor <;> word
  have Hvl : vs.length = c.n := by rw [Hnz] at Hif; omega
  rw [Hvl, Nat.sub_self, List.replicate_zero, List.append_nil]
  -- sorting, then the greedy matching
  wp_apply hsort.Ints e1 vs $$ [He1s] as %srt ⟨He1s, %Hperm, %Hsorted⟩
  · iframe He1s; ipureintro; omega
  have Hsl : srt.length = c.n := by rw [← Hperm.length_eq]; exact Hvl
  ihave %He1l := ownSlice_len $$ He1s
  ihave %He2l := ownSlice_len $$ He2s
  wp_apply (wp_slice_make2 (V := w64)) as %sq0 ⟨Hsq0, Hsqc0⟩
  · ipureintro; word
  ihave HI : (∃ (i : w64) (sq : GoSlice) (ps : List Nat), "i" ∷ i_ptr ↦ i ∗
      "sequence" ∷ sequence_ptr ↦ sq ∗ "Hsq" ∷ sq ↦* seqOf ps ∗
      "Hsqc" ∷ ownSliceCap w64 sq (DFrac.own 1) ∗
      "%Hi" ∷ ⌜sint.Z i = ps.length ∧ ps.length ≤ c.n ∧ ps.Nodup ∧ (∀ p ∈ ps, 1 ≤ p ∧ p ≤ c.n) ∧
        ps.map (mabF vs) = srt.take ps.length⌝ : IProp GF) $$ [i sequence Hsq0 Hsqc0]
  · iexists W64 0, sq0, []; iframe; ipureintro; simp
  wp_for HI
  wp_if_destruct
  · have Hil : ps.length < c.n := by rw [Hnz] at Hif; omega
    obtain ⟨jx, Hjx, Hjv, Hjn⟩ := mab_greedy_exists srt vs ps ps.length Hperm.symm (by omega) Hi.2.2.2.2
    ihave HJ : (∃ (jj : w64), "j" ∷ j_ptr ↦ jj ∗ "%Hjj" ∷ ⌜0 ≤ sint.Z jj ∧ sint.Z jj ≤ c.n ∧
        ∀ m, m < sint.nat jj → ¬ (vs[m]? = srt[ps.length]? ∧ (m + 1) ∉ ps)⌝ : IProp GF) $$ [j]
    · iexists W64 0; iframe; ipureintro; refine ⟨by word, by word, fun m hm => absurd hm (by word)⟩
    wp_for HJ
    wp_if_destruct
    · have Hjl : sint.Z jj < c.n := by rw [Hnz] at Hif; omega
      have Hbi : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z e1.len := ⟨by omega, by have := He1l.1; word⟩
      have Hbj : 0 ≤ sint.Z jj ∧ sint.Z jj < sint.Z e2.len := ⟨Hjj.1, by have := He2l.1; word⟩
      obtain ⟨x1, Hx1⟩ : ∃ x, srt[ps.length]? = some x := ⟨_, List.getElem?_eq_getElem (by omega)⟩
      obtain ⟨x2, Hx2⟩ : ∃ x, vs[sint.nat jj]? = some x := ⟨_, List.getElem?_eq_getElem (by word)⟩
      repeat' (first | wp_auto | simp only [Hbi, _root_.and_self, ↓reduceIte])
      wp_apply wp_load_slice_index e1 (sint.Z i) srt _ x1 Hbi.1 $$ [He1s] as He1s
      · iframe He1s; ipureintro; rw [show (sint.Z i).toNat = ps.length by omega]; exact Hx1
      repeat' (first | wp_auto | simp only [Hbj, _root_.and_self, ↓reduceIte])
      wp_apply wp_load_slice_index e2 (sint.Z jj) vs _ x2 Hbj.1 $$ [He2s] as He2s
      · iframe He2s; ipureintro; simpa using Hx2
      wp_if_destruct
      · subst Hif
        wp_apply wp_notInarray pr sq (seqOf ps) (jj + W64 1) $$ [Hsq] as Hsq
        · iexact Hsq
        have Hmem := mab_seqOf_mem ps (fun p hp => ⟨(Hi.2.2.2.1 p hp).1,
            by have := (Hi.2.2.2.1 p hp).2; omega⟩) jj Hjj.1 (by omega)
        wp_if_destruct
        · wp_for_post
          iframe
          iexists jj + W64 1; iframe; ipureintro
          refine ⟨by word, by word, fun m hm => ?_⟩
          rcases Nat.lt_or_ge m (sint.nat jj) with h | h
          · exact Hjj.2.2 m h
          · have : m = sint.nat jj := by word
            subst this; rintro ⟨-, h2⟩; exact h2 (Hmem.1 Hif)
        · have Hnin : (sint.nat jj + 1) ∉ ps := fun h => by simp only [Hmem] at Hif; exact Hif h
          wp_bind (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType go.int))))
            (Val (LiteralValueV _)))
          iapply wp_slice_literal (V := w64) (t := go.int) [jj + W64 1]
          wp_auto
          isplitl []
          · ipureintro; rfl
          iintro %lit_ptr ⟨Hlit, -⟩
          wp_apply wp_slice_append (V := w64) _ _ _ _ _ $$ [$Hsq $Hsqc $Hlit] as %sq' ⟨Hsq, Hsqc, -⟩
          wp_for_post
          wp_for_post
          rw [mab_seqOf_snoc ps jj Hjj.1 (by omega)]
          obtain ⟨Hnd', Hr', Hm'⟩ := mab_greedy_step srt vs ps ps.length (sint.nat jj) c.n Hvl (by word)
            (by rw [Hx2, Hx1]) (by omega) Hnin Hi.2.2.1 Hi.2.2.2.1 Hi.2.2.2.2
          iframe
          iexists i + W64 1, sq', ps ++ [sint.nat jj + 1]
          iframe; ipureintro
          simp only [List.length_append, List.length_singleton]
          exact ⟨by word, by omega, Hnd', Hr', Hm'⟩
      · wp_for_post
        iframe
        iexists jj + W64 1; iframe; ipureintro
        refine ⟨by word, by word, fun m hm => ?_⟩
        rcases Nat.lt_or_ge m (sint.nat jj) with h | h
        · exact Hjj.2.2 m h
        · have : m = sint.nat jj := by word
          subst this; rintro ⟨h1, -⟩; rw [Hx2, Hx1] at h1; exact Hif (Option.some.inj h1).symm
    exfalso
    have Hjn' : sint.nat jj = c.n := by rw [Hnz] at Hif; word
    exact Hjj.2.2 jx (by omega) ⟨Hjv, Hjn⟩
  -- the string
  have Hpl : ps.length = c.n := by rw [Hnz] at Hif; omega
  have Hperm' : isPerm c.n ps := mab_perm_of_nodup ps c.n Hi.2.2.1 Hi.2.2.2.1 Hpl
  have Hrps := Hi.2.2.2.1
  ihave %Hsql := ownSlice_len $$ Hsq
  have Hsqn : sq.len = W64 (c.n : Int) := by
    simp only [seqOf, List.length_map] at Hsql
    rw [Hpl] at Hsql
    have := Hsql.1
    rcases Hn35 with h | h <;> rw [h] at this ⊢ <;> word
  rw [Hsqn]
  wp_auto
  ihave HI : (∃ (i : w64), "i" ∷ i_ptr ↦ i ∗ "s" ∷ s_ptr ↦ mabAcc (ps.take (sint.nat i)) ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ c.n⌝ : IProp GF) $$ [i s]
  · iexists W64 0; iframe; ipureintro; word
  wp_for HI
  wp_if_destruct
  · have Hil : sint.Z i < c.n := by
      have : sint.Z i < sint.Z (W64 (c.n : Int)) := by simpa [intoVal_eq_iff] using Hif
      omega
    have Hbi : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z sq.len := ⟨Hi.1, by rw [Hsqn, Hnz]; exact Hil⟩
    obtain ⟨p, Hp⟩ : ∃ p, ps[sint.nat i]? = some p := ⟨_, List.getElem?_eq_getElem (by word)⟩
    have Hp5 : 1 ≤ p ∧ p ≤ c.n := Hrps p (List.mem_of_getElem? Hp)
    repeat' (first | wp_auto | simp only [Hbi, _root_.and_self, ↓reduceIte])
    wp_apply wp_load_slice_index sq (sint.Z i) (seqOf ps) _ (W64 (p : Int)) Hbi.1 $$ [Hsq] as Hsq
    · iframe Hsq; ipureintro; simp [seqOf, Hp]
    wp_apply wp_FormatInt_digit (W64 (p : Int)) (by word) (by word)
    rw [show sint.Z (W64 (p : Int)) = (p : Int) by word, ← mab_decimal_digit p Hp5.1 (by omega)]
    wp_for_post
    iframe
    iexists i + W64 1; iframe
    rw [show sint.nat (i + W64 1) = sint.nat i + 1 by word, List.take_add_one, Hp]
    simp only [Option.toList_some]
    rw [mabAcc_snoc]
    iframe; ipureintro; word
  have Hin : sint.nat i = ps.length := by
    have : ¬ sint.Z i < sint.Z (W64 (c.n : Int)) := by simpa [intoVal_eq_iff] using Hif
    rw [Hnz] at this; word
  rw [Hin, List.take_length]
  wp_func_call
  wp_auto
  have Hlen : (mabAcc ps).length = 2 * c.n := by
    rw [mabAcc_length ps (fun q hq => ⟨(Hrps q hq).1, by have := (Hrps q hq).2; omega⟩), Hpl]
  have Hl63 : (mabAcc ps).length < 2 ^ 63 := by omega
  simp only [Hl63, ↓reduceIte]
  rw [Hlen]
  have Hb : sint.Z (W64 1) ≤ sint.Z (W64 ((2 * c.n : Nat) : Int)) ∧
      sint.Z (W64 ((2 * c.n : Nat) : Int)) ≤ ((mabAcc ps).length : Int) := by
    rw [Hlen]; rcases Hn35 with h | h <;> rw [h] <;> decide
  have Hd : (sint.nat (W64 ((2 * c.n : Nat) : Int)) - 1) = (mabAcc ps).length - 1 := by
    rw [Hlen]; rcases Hn35 with h | h <;> rw [h] <;> rfl
  wp_auto
  simp only [Hb, _root_.and_self, ↓reduceIte, Hd, _root_.true_and]
  rw [List.take_of_length_le (by simp), mabAcc_drop ps (by intro h; rw [h] at Hpl; simp at Hpl; omega)]
  wp_auto
  iapply HΦ
  iframe
  isplitr
  · ipureintro; exact Hperm'
  iunfold epochOwn
  iexists et, ets; iframe

end proofs

end Perennial.raxos

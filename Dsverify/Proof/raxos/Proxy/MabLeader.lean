/-
Package `proxy`: leader mode 2's leader sequences (`proxymabhandler.go`): `isBeginningOfEpoch`,
`sequenceWithSelfLast`, `convertToIntArray`, `getLeaderSequenceFromLastEpoch`,
`getLeaderSequence`, `getLeaderWait`.
-/
module

public import Dsverify.Proof.raxos.Proxy.MabSpecs
public import Dsverify.Proof.raxos.Proxy.SumPure
public import Dsverify.Proof.raxos.Hyp
public import Perennial.Proof.strings.Link

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Perennial.raxos


open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open Perennial.raxos.pure Perennial.raxos.msg
open raxos.replica.src

/-! ## Pure facts -/

/-- `a + 1, ..., b` (as `int64`s). -/
def mlSeg (a b : Int) : List w64 :=
  (List.range (b - a).toNat).map fun (m : Nat) => W64 (a + (m : Int) + 1)

theorem mlSeg_snoc (a b : Int) (h : a ≤ b) : mlSeg a (b + 1) = mlSeg a b ++ [W64 (b + 1)] := by
  unfold mlSeg
  rw [show (b + 1 - a).toNat = (b - a).toNat + 1 by omega, List.range_succ, List.map_append]
  simp only [List.map_cons, List.map_nil]
  congr 3; omega

theorem mlSeg_self (a : Int) : mlSeg a a = [] := by simp [mlSeg]

theorem mlSeg_seqOf (a b : Nat) (h : a ≤ b) :
    mlSeg a b = seqOf (List.range' (a + 1) (b - a)) := by
  unfold mlSeg seqOf
  rw [show ((b : Int) - a).toNat = b - a by omega, List.range'_eq_map_range, List.map_map]
  apply List.map_congr_left
  intro m _
  simp only [Function.comp]
  congr 1; push_cast; omega

/-- The replicas rotated: `s + 1, ..., n, 1, ..., s`. -/
def rotSeq (n s : Nat) : List Nat := List.range' (s + 1) (n - s) ++ List.range' 1 s

theorem rotSeq_seqOf (n s : Nat) (h : s ≤ n) :
    mlSeg s n ++ mlSeg 0 s = seqOf (rotSeq n s) := by
  have h1 := mlSeg_seqOf s n h
  have h2 : mlSeg 0 s = seqOf (List.range' 1 s) := by
    simpa using mlSeg_seqOf 0 s (Nat.zero_le _)
  rw [h1, h2]; unfold rotSeq seqOf; rw [List.map_append]

theorem rotSeq_perm (n s : Nat) (h : s ≤ n) : isPerm n (rotSeq n s) := by
  unfold isPerm rotSeq
  have : List.range' 1 n = List.range' 1 s ++ List.range' (s + 1) (n - s) := by
    have := (List.range'_append (s := 1) (m := s) (n := n - s) (step := 1))
    rw [show 1 + 1 * s = s + 1 by omega, show s + (n - s) = n by omega] at this
    exact this.symm
  rw [this]
  exact List.perm_append_comm

theorem rotSeq_head (n s : Nat) (h : s < n) : (rotSeq n s).head? = some (s + 1) := by
  unfold rotSeq
  obtain ⟨m, hm⟩ : ∃ m, n - s = m + 1 := ⟨n - s - 1, by omega⟩
  rw [hm, List.range'_succ]; rfl

theorem rotSeq_head_self (n : Nat) (h : 1 < n) : (rotSeq n n).head? = some 1 := by
  unfold rotSeq
  obtain ⟨m, hm⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [Nat.sub_self, List.range'_zero, List.nil_append, hm, List.range'_succ]; rfl

theorem idxOf_min (k : Nat) (q : List Nat) (m : Nat) (h : m < q.idxOf k) : q[m]? ≠ some k := by
  induction q generalizing m with
  | nil => simp at h
  | cons a l ih =>
    rw [List.idxOf_cons] at h
    by_cases hak : a = k
    · subst hak; simp at h
    · cases m with
      | zero => simp [hak]
      | succ m => simp only [List.getElem?_cons_succ]; apply ih; simp [hak] at h; omega

theorem idxOf_zero (k : Nat) (q : List Nat) (hq : k ∈ q) : q.idxOf k = 0 ↔ q.head? = some k := by
  cases q with
  | nil => simp at hq
  | cons a l => rw [List.idxOf_cons]; by_cases hak : a = k <;> simp [hak]

theorem seqOf_getElem? (q : List Nat) (m : Nat) :
    (seqOf q)[m]? = (q[m]?).map (fun x : Nat => W64 (x : Int)) := by
  unfold seqOf; simp

/-- `","`. -/
def comma : GoString := [W8 44]
theorem splitAux_nocomma (d r field : GoString) (hd : W8 44 ∉ d) :
    strings.splitAux comma (d ++ r) field = strings.splitAux comma r (field ++ d) := by
  induction d generalizing field with
  | nil => simp
  | cons a d ih =>
    simp only [List.cons_append]
    rw [strings.splitAux]
    have ha : a ≠ W8 44 := fun h => hd (by simp [h])
    have : ¬ (comma ≠ [] ∧ comma <+: a :: (d ++ r)) := by
      rintro ⟨-, h⟩; apply ha; unfold comma at h; obtain ⟨t, ht⟩ := h; simp at ht; exact ht.1.symm
    simp only [this, ↓reduceIte]
    rw [ih _ (fun h => hd (List.mem_cons_of_mem _ h))]
    simp
theorem splitAux_comma (r field : GoString) :
    strings.splitAux comma (W8 44 :: r) field = field :: strings.splitAux comma r [] := by
  rw [strings.splitAux]
  have : comma ≠ [] ∧ comma <+: W8 44 :: r := ⟨by simp [comma], by simp [comma]⟩
  simp only [this, ne_eq]
  rfl
theorem split_intersperse (d : GoString) (ds : List GoString) (field : GoString)
    (h : ∀ x ∈ d :: ds, W8 44 ∉ x) :
    strings.splitAux comma (List.intersperse comma (d :: ds)).flatten field = (field ++ d) :: ds := by
  induction ds generalizing d field with
  | nil =>
    simp only [List.intersperse_singleton, List.flatten_cons, List.flatten_nil, List.append_nil]
    rw [show d = d ++ [] by simp, splitAux_nocomma _ _ _ (h d (by simp))]
    simp [strings.splitAux]
  | cons d2 rest ih =>
    rw [List.intersperse_cons_cons, List.flatten_cons, List.flatten_cons,
      splitAux_nocomma _ _ _ (h d (by simp))]
    rw [show comma ++ _ = W8 44 :: _ from rfl, splitAux_comma]
    have := ih d2 [] (fun x hx => h x (List.mem_cons_of_mem _ hx))
    simp only [List.nil_append] at this
    rw [show ([] : GoString).append (List.intersperse comma (d2 :: rest)).flatten =
      (List.intersperse comma (d2 :: rest)).flatten from rfl, this]

theorem split_seqStr (p : List Nat) (hp : p ≠ []) (hs : ∀ x ∈ p, 1 ≤ x ∧ x ≤ 5) :
    strings.split (seqStr p) go!"," = p.map decimal := by
  obtain ⟨d, ds, hd⟩ : ∃ d ds, p.map decimal = d :: ds := by
    cases p with
    | nil => exact absurd rfl hp
    | cons a l => exact ⟨_, _, rfl⟩
  unfold seqStr strings.split
  rw [show (go!"," : GoString) = comma from rfl, hd, split_intersperse]
  · rfl
  · intro x hx
    rw [← hd] at hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    exact (decimal_small y (hs y hy).1 (hs y hy).2).1

theorem rotSeq_head_ne (n k : Nat) (hn : 3 ≤ n) (hk : 1 ≤ k ∧ k ≤ n) :
    (rotSeq n k).head? ≠ some k := by
  rcases Nat.lt_or_eq_of_le hk.2 with h | h
  · rw [rotSeq_head n k h]; simp
  · subst h; rw [rotSeq_head_self _ (by omega)]; simp; omega

/-! ## Proofs -/

section proofs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [π : NetProtoGS] [qv : hyp.QpVocab GF]
variable [raxos.replica.src.Assumptions] [raxos.proto.client.Assumptions]
variable [ha : hyp.AtoiHyp GF]

attribute [local instance] HeapGS.goose_globalGS

theorem mab_decided_summary (γ : QNames) (c : QConf) (j : Int) (a : List GoString)
    (hj : sumSlot c.n c.ep j) :
    ⊢@{IProp GF} inv consN (consInv γ) -∗ confIs γ c -∗ decided γ j a ={⊤}=∗
      ⌜∃ p, isPerm c.n p ∧ a = [summaryId p]⌝ := by
  iintro #Hinv #Hc Hd
  imod (decided_summary γ ⊤ CoPset.subseteq_top c j a hj) $$ Hinv Hc Hd with %Hp
  imodintro; ipureintro; exact Hp

theorem wp_sequenceWithSelfLast (c : QConf) (k : Nat) (pr : Loc) :
  {{ isPkgInit (PROP := IProp GF) pkg_id.raxos.replica.src ∗ sharedConsts c k pr ∗
      ⌜c.ok ∧ 1 ≤ k ∧ k ≤ c.n⌝ }}
    (App (Val (pr @!! go.GoType.PointerType Proxy.ty @!! go!"sequenceWithSelfLast")) (Val #()))
  {{ (sl : GoSlice), RET #sl; sl ↦* seqOf (rotSeq c.n k) }} := by
  wp_start as ⟨#Hc, %Hk⟩
  iunfold sharedConsts at Hc
  icases Hc with ⟨#Hname, -, -, -, -, -, -, #Hnr⟩
  have Hok := Hk.1
  unfold QConf.ok at Hok
  wp_auto
  wp_apply (wp_slice_make2 (V := w64)) as %sl0 ⟨Hsl0, Hcap0⟩
  · ipureintro; word
  ihave HI : (∃ (j : w64) (rsl : GoSlice), "i" ∷ i_ptr ↦ j ∗ "rA" ∷ rA_ptr ↦ rsl ∗
      "Hrs" ∷ rsl ↦* mlSeg k (sint.Z j - 1) ∗ "Hrc" ∷ ownSliceCap w64 rsl (DFrac.own 1) ∗
      "%Hj" ∷ ⌜(k : Int) + 1 ≤ sint.Z j ∧ sint.Z j ≤ c.n + 1⌝ : IProp GF) $$ [i rA Hsl0 Hcap0]
  · iexists (W64 k + W64 1), sl0
    rw [show sint.Z (W64 (k : Int) + W64 1) - 1 = k by word, mlSeg_self]
    iframe; ipureintro; constructor <;> word
  wp_for HI
  wp_if_destruct
  · wp_bind (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType go.int64))))
      (Val (LiteralValueV _)))
    iapply wp_slice_literal (V := w64) (t := go.int64) [j]
    wp_auto
    isplitl []
    · ipureintro; rfl
    iintro %lit_ptr ⟨Hlit, -⟩
    wp_apply wp_slice_append (V := w64) _ _ _ _ _ $$ [$Hrs $Hrc $Hlit] as %rsl' ⟨Hrs, Hrc, -⟩
    wp_for_post
    iframe
    iexists j + W64 1, rsl'
    have Hjn : sint.Z j ≤ c.n := by
      have : sint.Z (W64 (c.n : Int)) = c.n := by word
      word
    rw [show sint.Z (j + W64 1) - 1 = (sint.Z j - 1) + 1 by word, mlSeg_snoc _ _ (by omega),
      show W64 (sint.Z j - 1 + 1) = j by word]
    iframe; ipureintro; constructor <;> word
  have Hjn : sint.Z j = c.n + 1 := by
    have : sint.Z (W64 (c.n : Int)) = c.n := by word
    word
  rw [Hjn, show (c.n : Int) + 1 - 1 = c.n by omega]
  ihave HI : (∃ (j : w64) (rsl : GoSlice), "i" ∷ i_ptr ↦ j ∗ "rA" ∷ rA_ptr ↦ rsl ∗
      "Hrs" ∷ rsl ↦* (mlSeg k c.n ++ mlSeg 0 (sint.Z j - 1)) ∗
      "Hrc" ∷ ownSliceCap w64 rsl (DFrac.own 1) ∗
      "%Hj" ∷ ⌜1 ≤ sint.Z j ∧ sint.Z j ≤ k + 1⌝ : IProp GF) $$ [i rA Hrs Hrc]
  · iexists W64 1, rsl
    rw [show sint.Z (W64 1) - 1 = 0 from rfl, mlSeg_self, List.append_nil]; iframe; ipureintro
    constructor <;> word
  wp_for HI
  wp_if_destruct
  · wp_bind (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType go.int64))))
      (Val (LiteralValueV _)))
    iapply wp_slice_literal (V := w64) (t := go.int64) [j]
    wp_auto
    isplitl []
    · ipureintro; rfl
    iintro %lit_ptr ⟨Hlit, -⟩
    wp_apply wp_slice_append (V := w64) _ _ _ _ _ $$ [$Hrs $Hrc $Hlit] as %rsl' ⟨Hrs, Hrc, -⟩
    wp_for_post
    iframe
    iexists j + W64 1, rsl'
    have Hjk : sint.Z j ≤ k := by
      have : sint.Z (W64 (k : Int)) = k := by word
      word
    rw [show sint.Z (j + W64 1) - 1 = (sint.Z j - 1) + 1 by word, mlSeg_snoc _ _ (by omega),
      show W64 (sint.Z j - 1 + 1) = j by word, List.append_assoc]
    iframe; ipureintro; constructor <;> word
  have Hjk : sint.Z j = k + 1 := by
    have : sint.Z (W64 (k : Int)) = k := by word
    word
  rw [Hjk, show (k : Int) + 1 - 1 = k by omega, rotSeq_seqOf c.n k Hk.2.2]
  wp_end

theorem sdiv_small (i e : w64) (_hi : 0 ≤ sint.Z i) (he : 0 < sint.Z e) :
    sint.Z (BitVec.sdiv i e) = (sint.Z i).tdiv (sint.Z e) := by
  have h : e ≠ -1#64 := by rintro rfl; exact absurd he (by decide)
  rw [show sint.Z (BitVec.sdiv i e) = (BitVec.sdiv i e).toInt from rfl,
    BitVec.toInt_sdiv_of_ne_or_ne _ _ (Or.inr h)]

theorem wp_isBeginningOfEpoch : isBeginningOfEpoch_spec (GF := GF) (hG := hG) := by
  intro c k pr i
  wp_start as ⟨#Hc, %Hi⟩
  iunfold sharedConsts at Hc
  icases Hc with ⟨#Hname, -, -, -, -, -, #Hep, #Hnr⟩
  have Hok := Hi.1
  unfold QConf.ok at Hok
  wp_auto
  have Hep : sint.Z (W64 (c.ep : Int)) = c.ep := by word
  have Hn : sint.Z (W64 2 * W64 (c.n : Int)) = 2 * c.n := by word
  have Hd := sdiv_small i (W64 c.ep) Hi.2.1 (by omega)
  rw [Hep] at Hd
  have Hd0 : 0 ≤ (sint.Z i).tdiv c.ep := Int.tdiv_nonneg Hi.2.1 (by omega)
  have Hep0 : ¬ sint.Z (W64 (c.ep : Int)) = 0 := by omega
  repeat' (first | wp_auto | simp only [Hep0, ↓reduceIte])
  generalize Hq : (sint.Z i).tdiv c.ep = q at Hd Hd0
  wp_if_destruct
  · have Hge : 2 * (c.n : Int) ≤ q := by
      have : sint.Z (W64 2 * W64 (c.n : Int)) ≤ sint.Z (BitVec.sdiv i (W64 (c.ep : Int))) := by
        simpa using Hif
      omega
    have Hmul : sint.Z (BitVec.sdiv i (W64 (c.ep : Int)) * W64 (c.ep : Int)) = q * c.ep := by
      have h1 : q * c.ep ≤ sint.Z i := by
        rw [← Hq, Int.tdiv_eq_ediv_of_nonneg Hi.2.1]; exact Int.ediv_mul_le _ (by omega)
      have h2 : 0 ≤ q * c.ep := Int.mul_nonneg Hd0 (by omega)
      generalize BitVec.sdiv i (W64 (c.ep : Int)) = d at Hd ⊢
      generalize W64 (c.ep : Int) = e at Hep ⊢
      have h3 : 0 ≤ sint.Z d * sint.Z e ∧ sint.Z d * sint.Z e ≤ 100000 := by
        rw [Hd, Hep]; omega
      rw [← Hd, ← Hep]
      word
    have Hiff : i = BitVec.sdiv i (W64 (c.ep : Int)) * W64 (c.ep : Int) ↔ sint.Z i = q * c.ep := by
      rw [← Hmul]; exact ⟨fun h => by rw [← h], fun h => by word⟩
    wp_if_destruct
    · have : sumSlot c.n c.ep (sint.Z i) := ⟨by omega, by rw [Hq]; exact Hiff.1 Hif⟩
      rw [decide_eq_true this]; iapply HΦ; itrivial
    · have : ¬ sumSlot c.n c.ep (sint.Z i) := fun ⟨_, h⟩ => Hif (Hiff.2 (by rw [← Hq]; exact h))
      rw [decide_eq_false this]; iapply HΦ; itrivial
  · have : ¬ sumSlot c.n c.ep (sint.Z i) := by
      rintro ⟨h, -⟩; apply Hif; rw [Hn, Hd, ← Hq]; exact h
    rw [decide_eq_false this]; iapply HΦ; itrivial

theorem wp_getLeaderWait : getLeaderWait_spec (GF := GF) (hG := hG) := by
  intro c k pr sl q
  wp_start as ⟨#Hc, %Hk, Hsl⟩
  iunfold sharedConsts at Hc
  icases Hc with ⟨#Hname, -, -, -, #Hmode, #Hto, -, -⟩
  have Hok := Hk.1
  unfold QConf.ok at Hok
  wp_auto
  have Hkq : k ∈ q := (isPerm_mem c.n q Hk.2.2.2 k).2 ⟨Hk.2.1, Hk.2.2.1⟩
  have Hql := isPerm_length c.n q Hk.2.2.2
  have Hidx : q.idxOf k < q.length := List.idxOf_lt_length_of_mem Hkq
  have Hat : q[q.idxOf k]? = some k := by
    rw [List.getElem?_eq_getElem Hidx, List.getElem_idxOf Hidx]
  have Hsmall : ∀ (m x : Nat), q[m]? = some x → x ≤ 5 := by
    intro m x h
    have := (isPerm_mem c.n q Hk.2.2.2 x).1 (List.mem_of_getElem? h); omega
  ihave %Hlen := ownSlice_len $$ Hsl
  have Hsl_len : (seqOf q).length = q.length := by simp [seqOf]
  ihave HI : (∃ (jj : w64), "j" ∷ j_ptr ↦ jj ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z jj ∧ sint.Z jj ≤ q.idxOf k⌝ : IProp GF) $$ [j]
  · iexists W64 0; iframe; ipureintro; exact ⟨by word, by word⟩
  wp_for HI
  wp_if_destruct
  · have Hjq : sint.nat jj < q.length := by word
    obtain ⟨x, Hqx⟩ : ∃ x, q[sint.nat jj]? = some x := ⟨_, List.getElem?_eq_getElem Hjq⟩
    have Hx : (seqOf q)[sint.nat jj]? = some (W64 (x : Int)) := by rw [seqOf_getElem?, Hqx]; rfl
    have Hb : 0 ≤ sint.Z jj ∧ sint.Z jj < sint.Z sl.len := ⟨Hj.1, by word⟩
    repeat' (first | wp_auto | simp only [Hb, _root_.and_self, ↓reduceIte])
    wp_apply wp_load_slice_index sl (sint.Z jj) (seqOf q) _ _ Hj.1 $$ [Hsl] as Hsl
    · iframe Hsl; ipureintro; rw [show (sint.Z jj).toNat = sint.nat jj by word]; exact Hx
    have Hxs := Hsmall _ _ Hqx
    wp_if_destruct
    · -- found: `jj` is the rank
      have Hqk : x = k := by
        have h1 : sint.Z (W64 (x : Int)) = x := by word
        have h2 : sint.Z (W64 (k : Int)) = k := by word
        have : (x : Int) = k := by rw [← h1, ← h2, Hif]
        omega
      subst Hqk
      have Hjr : sint.nat jj = q.idxOf x := by
        rcases Nat.lt_or_eq_of_le (show sint.nat jj ≤ q.idxOf x by word) with h | h
        · exact absurd Hqx (idxOf_min x q _ h)
        · exact h
      have Hw : W64 (c.tmo : Int) * jj = W64 ((c.tmo : Int) * (q.idxOf x : Int)) := by
        rw [← Hjr, Int.toNat_of_nonneg Hj.1]
        exact w64_mul_small c.tmo jj (by omega) Hj.1 (by have := Hidx; omega)
      wp_for_post
      rw [Hw]
      iapply HΦ
      iframe
      ipureintro; omega
    · have Hne : sint.nat jj ≠ q.idxOf k := by
        intro h
        apply Hif
        rw [h, Hat] at Hqx; cases Hqx; rfl
      wp_for_post
      iframe
      iexists jj + W64 1; iframe; ipureintro; constructor <;> word
  · exfalso; apply Hif; have : sint.Z jj < sint.Z sl.len := by
      have : sint.nat jj ≤ q.idxOf k := by word
      word
    simp [this]

theorem wp_convertToIntArray (c : QConf) (k : Nat) (pr : Loc)
    (p : List Nat) :
  {{ isPkgInit (PROP := IProp GF) pkg_id.raxos.replica.src ∗ sharedConsts c k pr ∗
      ⌜c.ok ∧ isPerm c.n p⌝ }}
    (App (Val (pr @!! go.GoType.PointerType Proxy.ty @!! go!"convertToIntArray"))
      (Val #(summaryId p)))
  {{ (sl : GoSlice), RET #sl; sl ↦* seqOf p }} := by
  wp_start as ⟨#Hc, %Hp⟩
  iunfold sharedConsts at Hc
  icases Hc with ⟨#Hname, -, -, -, -, -, -, #Hnr⟩
  have Hok := Hp.1
  unfold QConf.ok at Hok
  have Hpl := isPerm_length c.n p Hp.2
  have Hps : ∀ x ∈ p, 1 ≤ x ∧ x ≤ 5 := fun x hx => by
    have := (isPerm_mem c.n p Hp.2 x).1 hx; omega
  have Hpne : p ≠ [] := by intro h; rw [h] at Hpl; simp at Hpl; omega
  ihave #Hstr : isPkgInit (PROP := IProp GF) pkg_id.strings $$ []
  · iPkgInit
  wp_auto
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len with %Hlen
  have Hid : summaryId p = go!"Epoch" ++ seqStr p := rfl
  have Hl5 : 5 ≤ (summaryId p).length := by rw [Hid]; simp
  have Hb : 0 ≤ sint.Z (W64 5) ∧ sint.Z (W64 5) ≤ sint.Z (W64 ((summaryId p).length : Int)) ∧
      sint.Z (W64 ((summaryId p).length : Int)) ≤ (summaryId p).length := by
    refine ⟨by word, by word, by word⟩
  have Hsub : List.take (sint.nat (W64 ((summaryId p).length : Int)) - 5)
      (List.drop 5 (summaryId p)) = seqStr p := by
    rw [show sint.nat (W64 ((summaryId p).length : Int)) = (summaryId p).length by word, Hid]
    simp
  repeat' (first | wp_auto | simp only [Hb, Hsub, _root_.and_self, ↓reduceIte])
  wp_apply (strings.wp_Split (seqStr p) go!"," (by simp)) as %ssl ⟨Hs, -⟩
  rw [split_seqStr p Hpne Hps]
  wp_apply (wp_slice_make2 (V := w64)) as %ia ⟨Hia, -⟩
  · ipureintro; word
  ihave %Hslen := ownSlice_len $$ Hs
  have Hn : sint.Z (W64 (c.n : Int)) = c.n := by word
  wp_if_destruct
  rotate_left
  · exfalso; apply Hif
    have : sint.nat ssl.len = c.n := by rw [← Hslen.1]; simp [Hpl]
    word
  ihave HI : (∃ (i : w64) (xs : List w64), "i" ∷ i_ptr ↦ i ∗ "Hia" ∷ ia ↦* xs ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ c.n ∧ xs.length = c.n ∧
        ∀ m, m < sint.nat i → xs[m]? = (seqOf p)[m]?⌝ : IProp GF) $$ [i Hia]
  · iexists W64 0, _; iframe; ipureintro
    refine ⟨by word, by word, by simp; word, fun m hm => ?_⟩
    have : sint.nat (W64 0) = 0 := rfl
    omega
  wp_for HI
  wp_if_destruct
  · have Hip : sint.nat i < p.length := by word
    obtain ⟨x, Hx⟩ : ∃ x, p[sint.nat i]? = some x := ⟨_, List.getElem?_eq_getElem Hip⟩
    have Hxs := Hps x (List.mem_of_getElem? Hx)
    have Hb2 : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z ssl.len := ⟨Hi.1, by simp at Hslen; word⟩
    repeat' (first | wp_auto | simp only [Hb2, _root_.and_self, ↓reduceIte])
    wp_apply wp_load_slice_index ssl (sint.Z i) (p.map decimal) _ (decimal x) Hi.1 $$ [Hs] as Hs
    · iframe Hs; ipureintro
      rw [show (sint.Z i).toNat = sint.nat i by word, List.getElem?_map, Hx]; rfl
    obtain ⟨-, Hsd, Hdv⟩ := decimal_small x Hxs.1 Hxs.2
    wp_apply ha.Atoi (decimal x) Hsd
    rw [Hdv]
    ihave %Hial := ownSlice_len $$ Hia
    have Hb3 : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z ia.len := ⟨Hi.1, by word⟩
    simp only [Hb3, _root_.and_self, ↓reduceIte]
    wp_apply wp_store_slice_index $$ [Hia] as Hia
    · iframe Hia; ipureintro; exact ⟨Hi.1, by omega⟩
    wp_for_post
    iframe
    iexists i + W64 1, _
    iframe
    ipureintro
    refine ⟨by word, by word, by simp [Hi.2.2.1], fun m hm => ?_⟩
    rw [List.getElem?_set]
    by_cases hmi : sint.nat i = m
    · subst hmi; simp [Hi.2.2.1, show sint.nat i < c.n by omega, seqOf_getElem?, Hx]
    · rw [ite_eq_right (by omega)]; apply Hi.2.2.2; word
  have Hin : sint.nat i = c.n := by
    have : ¬ sint.Z i < sint.Z (W64 (c.n : Int)) := by simpa using Hif
    word
  have Hxs : xs = seqOf p := by
    apply List.ext_getElem?
    intro m
    by_cases hm : m < c.n
    · exact Hi.2.2.2 m (by omega)
    · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by simp [seqOf, Hpl]; omega)]
  subst Hxs
  iapply HΦ; iexact Hia

instance mab_ite_persistent {b : Prop} [Decidable b] (P Q : IProp GF) [Persistent P]
    [Persistent Q] : Persistent (if b then P else Q) := by
  split <;> infer_instance

instance mab_slotP_persistent (γ : QNames) (γs : GName) (c : QConf) (i : Nat) (s : Slot)
    (o : Option (List GoString)) : Persistent (slotP (GF := GF) γ γs c i s o) := by
  unfold slotP idP decided evIn; cases o <;> simp only <;> infer_instance

instance mab_logP_persistent (γ : QNames) (γs : GName) (c : QConf) (slots : List Slot)
    (L : List (Option (List GoString))) : Persistent (logP (GF := GF) γ γs c slots L) := by
  unfold logP; infer_instance

theorem wp_getLeaderSequenceFromLastEpoch (γ : QNames) (γs : GName)
    (c : QConf) (k : Nat) (pr : Loc) (e : w64) (rl : GoSlice) (slots : List Slot)
    (L : List (Option (List GoString))) :
  {{ isPkgInit (PROP := IProp GF) pkg_id.raxos.replica.src ∗ sharedConsts c k pr ∗
      ⌜c.ok ∧ 1 ≤ k ∧ k ≤ c.n ∧ 2 * (c.n : Int) < sint.Z e ∧ sint.Z e ≤ 100000⌝ ∗
      inv consN (consInv γ) ∗ confIs γ c ∗ logRd γ γs c pr rl slots L }}
    (App (Val (pr @!! go.GoType.PointerType Proxy.ty @!! go!"getLeaderSequenceFromLastEpoch"))
      (Val #e))
  {{ (sl : GoSlice) (q : List Nat), RET #sl; sl ↦* seqOf q ∗ ⌜isPerm c.n q⌝ ∗
      (if decide (q.head? = some k) then decided γ ((sint.Z e - 1) * c.ep) [summaryId q]
        else iprop(True)) ∗
      logRd γ γs c pr rl slots L }} := by
  wp_start as ⟨#Hc, %Hk, #Hcons, #Hconf, Hlog⟩
  ihave #Hc2 := Hc
  iunfold sharedConsts at Hc2
  icases Hc2 with ⟨#Hname, -, -, -, -, -, #Hep, #Hnr⟩
  have Hok := Hk.1
  unfold QConf.ok at Hok
  iunfold logRd at Hlog
  icases Hlog with ⟨Hrl, Hsl, #Hlog⟩
  wp_auto
  have Hep : sint.Z (W64 (c.ep : Int)) = c.ep := by word
  have He1 : sint.Z (e - W64 1) = sint.Z e - 1 := by word
  have Hidx : sint.Z ((e - W64 1) * W64 (c.ep : Int)) = (sint.Z e - 1) * c.ep := by
    rw [w64_mul_toInt _ _ (by rw [He1]; omega) (by rw [Hep]; omega), He1, Hep]
  generalize Hix : (e - W64 1) * W64 (c.ep : Int) = idx at Hidx
  have Hidx0 : 0 < sint.Z idx := by rw [Hidx]; exact Int.mul_pos (by omega) (by omega)
  have Hsum : sumSlot c.n c.ep (sint.Z idx) := by
    unfold sumSlot
    rw [Hidx, Int.mul_tdiv_cancel _ (by omega)]
    omega
  wp_if_destruct
  · -- not in the log yet: the replica last
    wp_apply wp_sequenceWithSelfLast c k pr $$ [] as %sl Hsl'
    · iframe #; ipureintro; exact ⟨Hk.1, Hk.2.1, Hk.2.2.1⟩
    iapply HΦ
    iframe Hsl'
    isplitr
    · ipureintro; exact rotSeq_perm _ _ Hk.2.2.1
    rw [decide_eq_false (rotSeq_head_ne _ _ (by omega) ⟨Hk.2.1, Hk.2.2.1⟩)]
    simp only [Bool.false_eq_true, ↓reduceIte]
    isplitr
    · itrivial
    iunfold logRd; iframe Hrl Hsl Hlog
  ihave %Hrllen := ownSlice_len $$ Hsl
  have Hilt : sint.nat idx < slots.length := by word
  list_elem slots (sint.nat idx) as sx
  have Hb : 0 ≤ sint.Z idx ∧ sint.Z idx < sint.Z rl.len := ⟨by omega, by word⟩
  icases ownSlice_elem_acc (sint.Z idx) sx rl _ slots Hb.1 (by simpa using Hsx_lookup) $$ Hsl
    with ⟨Hel, Hsl⟩
  repeat' (first | wp_auto | simp only [Hb, _root_.and_self, ↓reduceIte])
  ihave Hsl := Hsl $$ Hel
  rw [list_set_lookup_self _ _ _ (by simpa using Hsx_lookup)]
  wp_if_destruct
  rotate_left
  · -- not decided here yet: the replica last
    wp_apply wp_sequenceWithSelfLast c k pr $$ [] as %sl Hsl'
    · iframe #; ipureintro; exact ⟨Hk.1, Hk.2.1, Hk.2.2.1⟩
    iapply HΦ
    iframe Hsl'
    isplitr
    · ipureintro; exact rotSeq_perm _ _ Hk.2.2.1
    rw [decide_eq_false (rotSeq_head_ne _ _ (by omega) ⟨Hk.2.1, Hk.2.2.1⟩)]
    simp only [Bool.false_eq_true, ↓reduceIte]
    isplitr
    · itrivial
    iunfold logRd; iframe Hrl Hsl Hlog
  -- decided: the summary of the previous epoch's first slot
  iunfold logP at Hlog
  icases Hlog with ⟨%HlenL, #Hlog'⟩
  ihave Hs := BigSepL.bigSepL_lookup_acc (by simpa using Hsx_lookup) $$ Hlog'
  icases Hs with ⟨⟨%o, %Ho, #Hslot⟩, -⟩
  iunfold slotP at Hslot
  icases Hslot with ⟨%Hdo, Hslot⟩
  cases o with
  | none => rw [Hif] at Hdo; simp at Hdo
  | some ids =>
  icases Hslot with ⟨#Hdb, %Hids, #Hdec⟩
  have Hi0 : sint.nat idx ≠ 0 := by have := Hidx0; word
  simp only [Hi0, ↓reduceIte]
  rw [show ((sint.nat idx : Nat) : Int) = sint.Z idx by word]
  imod (mab_decided_summary γ c (sint.Z idx) ids Hsum) $$ Hcons Hconf Hdec with %Hp
  obtain ⟨p, Hpp, rfl⟩ := Hp
  icases ownSlice_elem_acc (sint.Z idx) sx rl _ slots Hb.1 (by simpa using Hsx_lookup) $$ Hsl
    with ⟨Hel, Hsl⟩
  repeat' (first | wp_auto | simp only [Hb, _root_.and_self, ↓reduceIte])
  ihave Hsl := Hsl $$ Hel
  rw [list_set_lookup_self _ _ _ (by simpa using Hsx_lookup)]
  ihave %Hdl := ownSlice_len $$ Hdb
  have Hb0 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z sx.decidedBatch'.len := by
    simp at Hdl; constructor <;> word
  simp only [Hb0, _root_.and_self, ↓reduceIte]
  wp_apply wp_load_slice_index _ (sint.Z (W64 0)) [summaryId p] _ (summaryId p) (by word) $$ [Hdb]
    as -
  · iframe Hdb; ipureintro; rfl
  wp_apply wp_convertToIntArray c k pr p $$ [] as %sl Hsl'
  · iframe #; ipureintro; exact ⟨Hk.1, Hpp⟩
  iapply HΦ
  iframe Hsl'
  isplitr
  · ipureintro; exact Hpp
  isplitr
  · rw [← Hidx]
    cases decide (p.head? = some k)
    · simp only [Bool.false_eq_true, ↓reduceIte]; itrivial
    · simp only [↓reduceIte]; iexact Hdec
  iunfold logRd; iframe Hrl Hsl
  iunfold logP; iframe Hlog'; ipureintro; exact HlenL

theorem mab_leadEv_rr (γ : QNames) (c : QConf) (i me : Int) (h : i.tdiv c.ep ≤ 2 * c.n)
    (hme : me = rrLeader c.n c.ep i) : ⊢@{IProp GF} leadEv γ c i me :=
  leadEv_rr γ c i me h hme

theorem mab_leadEv_sum (γ : QNames) (c : QConf) (i me : Int) (p : List Nat)
    (h : 2 * (c.n : Int) < i.tdiv c.ep) (hp : isPerm c.n p)
    (hme : p.head?.map (fun k : Nat => (k : Int)) = some me) :
    ⊢@{IProp GF} decided γ ((i.tdiv c.ep - 1) * c.ep) [summaryId p] -∗ leadEv γ c i me :=
  leadEv_sum γ c i me p h hp hme

theorem wp_getLeaderSequence :
    getLeaderSequence_spec (GF := GF) (hG := hG) := by
  intro γ γs c k pr i rl slots L
  wp_start as ⟨#Hc, %Hk, #Hcons, #Hconf, Hlog⟩
  ihave #Hc2 := Hc
  iunfold sharedConsts at Hc2
  icases Hc2 with ⟨#Hname, -, -, -, #Hmode, -, #Hep, #Hnr⟩
  have Hok := Hk.1
  unfold QConf.ok at Hok
  wp_auto
  have Hep : sint.Z (W64 (c.ep : Int)) = c.ep := by word
  have Hnn : sint.Z (W64 (c.n : Int)) = c.n := by word
  have Hep0 : ¬ sint.Z (W64 (c.ep : Int)) = 0 := by omega
  have Hd := sdiv_small i (W64 c.ep) Hk.2.2.2.1 (by omega)
  rw [Hep] at Hd
  have Hd0 : 0 ≤ (sint.Z i).tdiv c.ep := Int.tdiv_nonneg Hk.2.2.2.1 (by omega)
  have Hdle : (sint.Z i).tdiv c.ep ≤ sint.Z i := by
    rw [Int.tdiv_eq_ediv_of_nonneg Hk.2.2.2.1]; exact Int.ediv_le_self _ Hk.2.2.2.1
  repeat' (first | wp_auto | simp only [Hep0, ↓reduceIte])
  generalize Hq : (sint.Z i).tdiv c.ep = q at Hd Hd0 Hdle
  generalize Hev : BitVec.sdiv i (W64 (c.ep : Int)) = ev at Hd
  have H2n : sint.Z (W64 2 * W64 (c.n : Int)) = 2 * c.n := by word
  wp_if_destruct
  · -- round robin
    have Hqle : q ≤ 2 * c.n := by rw [← Hd, ← H2n]; simpa using Hif
    have Hs : sint.Z (ev.srem (W64 (c.n : Int))) = q.tmod c.n := by
      rw [show sint.Z (ev.srem (W64 (c.n : Int))) = (ev.srem (W64 (c.n : Int))).toInt from rfl,
        BitVec.toInt_srem]
      change (sint.Z ev).tmod (sint.Z (W64 (c.n : Int))) = _
      rw [Hd, Hnn]
    generalize ev.srem (W64 (c.n : Int)) = sv at Hs ⊢
    have Hs0 : 0 ≤ q.tmod c.n := Int.tmod_nonneg _ Hd0
    have Hsn : q.tmod c.n < c.n := Int.tmod_lt_of_pos _ (by omega)
    have Hn0 : ¬ sint.Z (W64 (c.n : Int)) = 0 := by omega
    repeat' (first | wp_auto | simp only [Hn0, ↓reduceIte])
    wp_apply (wp_slice_make2 (V := w64)) as %sl0 ⟨Hsl0, Hcap0⟩
    · ipureintro; word
    ihave HI : (∃ (j : w64) (rsl : GoSlice), "i" ∷ i_ptr ↦ j ∗ "rA" ∷ rA_ptr ↦ rsl ∗
        "Hrs" ∷ rsl ↦* mlSeg (sint.Z sv) (sint.Z j) ∗ "Hrc" ∷ ownSliceCap w64 rsl (DFrac.own 1) ∗
        "%Hj" ∷ ⌜sint.Z sv ≤ sint.Z j ∧ sint.Z j ≤ c.n⌝ : IProp GF) $$ [i rA Hsl0 Hcap0]
    · iexists sv, sl0; rw [mlSeg_self]; iframe; ipureintro; omega
    irename «instance» => Hinst
    wp_for HI
    wp_if_destruct
    · wp_bind (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType go.int64))))
        (Val (LiteralValueV _)))
      iapply wp_slice_literal (V := w64) (t := go.int64) [j + W64 1]
      wp_auto
      isplitl []
      · ipureintro; rfl
      iintro %lit_ptr ⟨Hlit, -⟩
      wp_apply wp_slice_append (V := w64) _ _ _ _ _ $$ [$Hrs $Hrc $Hlit] as %rsl' ⟨Hrs, Hrc, -⟩
      wp_for_post
      iframe
      iexists j + W64 1, rsl'
      have Hjn : sint.Z j < c.n := by rw [← Hnn]; simpa using Hif
      rw [show sint.Z (j + W64 1) = sint.Z j + 1 by word, mlSeg_snoc _ _ Hj.1,
        show W64 (sint.Z j + 1) = j + W64 1 by word]
      iframe; ipureintro; omega
    have Hjn : sint.Z j = c.n := by
      have : ¬ sint.Z j < sint.Z (W64 (c.n : Int)) := by simpa using Hif
      omega
    rw [Hjn]
    ihave HI : (∃ (j : w64) (rsl : GoSlice), "i" ∷ i_ptr ↦ j ∗ "rA" ∷ rA_ptr ↦ rsl ∗
        "Hrs" ∷ rsl ↦* (mlSeg (sint.Z sv) c.n ++ mlSeg 0 (sint.Z j)) ∗
        "Hrc" ∷ ownSliceCap w64 rsl (DFrac.own 1) ∗
        "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z sv⌝ : IProp GF) $$ [i rA Hrs Hrc]
    · iexists W64 0, rsl
      rw [show sint.Z (W64 0) = 0 from rfl, mlSeg_self, List.append_nil]; iframe; ipureintro; omega
    wp_for HI
    wp_if_destruct
    · wp_bind (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType go.int64))))
        (Val (LiteralValueV _)))
      iapply wp_slice_literal (V := w64) (t := go.int64) [j + W64 1]
      wp_auto
      isplitl []
      · ipureintro; rfl
      iintro %lit_ptr ⟨Hlit, -⟩
      wp_apply wp_slice_append (V := w64) _ _ _ _ _ $$ [$Hrs $Hrc $Hlit] as %rsl' ⟨Hrs, Hrc, -⟩
      wp_for_post
      iframe
      iexists j + W64 1, rsl'
      rw [show sint.Z (j + W64 1) = sint.Z j + 1 by word, mlSeg_snoc _ _ Hj.1,
        show W64 (sint.Z j + 1) = j + W64 1 by word, List.append_assoc]
      iframe; ipureintro; word
    have Hj' : sint.Z j = sint.Z sv := by word
    obtain ⟨sn, Hsn'⟩ : ∃ sn : Nat, sint.Z sv = sn := ⟨(sint.Z sv).toNat, by omega⟩
    rw [Hj', Hsn', show ((c.n : Nat) : Int) = (c.n : Int) from rfl,
      rotSeq_seqOf c.n sn (by omega)]
    iapply HΦ
    iframe
    isplitr
    · ipureintro; exact rotSeq_perm _ _ (by omega)
    rw [rotSeq_head _ _ (by omega)]
    by_cases hh : some (sn + 1) = some k
    · rw [decide_eq_true hh]; simp only [↓reduceIte]
      have : sn + 1 = k := by simpa using hh
      iapply mab_leadEv_rr
      · rw [Hq]; exact Hqle
      · unfold rrLeader; rw [Hq]; omega
    · rw [decide_eq_false hh]; simp only [Bool.false_eq_true, ↓reduceIte]; itrivial
  · -- the summary of the previous epoch
    have Hqgt : 2 * (c.n : Int) < q := by
      have : ¬ sint.Z ev ≤ sint.Z (W64 2 * W64 (c.n : Int)) := by simpa using Hif
      omega
    wp_apply wp_getLeaderSequenceFromLastEpoch γ γs c k pr ev rl slots L $$ [Hlog]
      as %sl %q' ⟨Hsl, %Hq', Hld, Hlog⟩
    · iframe #; iframe; ipureintro; exact ⟨Hk.1, Hk.2.1, Hk.2.2.1, by omega, by omega⟩
    iapply HΦ
    iframe
    isplitr
    · ipureintro; exact Hq'
    by_cases hh : q'.head? = some k
    · rw [decide_eq_true hh]; simp only [↓reduceIte]
      have : q'.head? = some k := hh
      iapply mab_leadEv_sum γ c (sint.Z i) k q' (by rw [Hq]; exact Hqgt) Hq' (by rw [this]; rfl)
      rw [Hq, ← Hd]; iexact Hld
    · rw [decide_eq_false hh]; simp only [Bool.false_eq_true, ↓reduceIte]; itrivial

end proofs

end Perennial.raxos

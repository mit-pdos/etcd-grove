/-
Proof of `KvRaft/Spec/github_com/mit_pdos/etcd_grove/examples/raft/kvraft/GetStatus.lean`: the any-bytes
decoders in a chain (each given whatever the one before left, a nil rest after a failure), then the two
counter loops (`getUint64.specAny`, any rest), the conf state kept in the status's `Conf` field.
-/
module

public import KvRaft.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.TransportDefs
public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.GetStatus
public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.getUint64Any
public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.getConfStateAny
public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.getMapAny

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvraft

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Assumptions]

/-- What a caller chaining decoders keeps of `getUint64.specAny`'s post: the rest holds some bytes. -/
theorem getUint64_post_any (b rest : GoSlice) (dq : DFrac) (bs : List w8) (ok : Bool) :
    (if ok then ⌜bs = u64Le x ++ bs.drop 8⌝ ∗ rest ↦*{dq} bs.drop 8 ∗
        (rest ↦*{dq} bs.drop 8 -∗ b ↦*{dq} bs)
      else ⌜bs.length < 8 ∧ rest = slice.nil⌝ ∗ b ↦*{dq} bs : IProp GF) ⊢
    ∃ r : List w8, rest ↦*{dq} r := by
  cases ok with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    iintro ⟨%Hn, -⟩
    obtain ⟨-, Hn⟩ := Hn
    subst Hn
    iexists []
    iapply ownSlice_nil
  | true =>
    simp only [↓reduceIte]
    iintro ⟨-, Hr, -⟩
    iexists _
    iexact Hr

/-- What `GetStatus` keeps of `getConfState.specAny`'s post. -/
theorem getConfState_post_any (p : Loc) (rest : GoSlice) (dq : DFrac) (ok : Bool) :
    (if ok then ∃ (c : ConfStateM) (r : List w8), csPts p (DFrac.own 1) c true ∗ rest ↦*{dq} r
      else ⌜rest = slice.nil⌝ : IProp GF) ⊢
    ∃ r : List w8, rest ↦*{dq} r ∗
      (if ok then ∃ c : ConfStateM, csPts p (DFrac.own 1) c true else True) := by
  cases ok with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    iintro %Hn
    subst Hn
    iexists []
    isplitl
    · iapply ownSlice_nil
    itrivial
  | true =>
    simp only [↓reduceIte]
    iintro ⟨%c, %r, Hc, Hr⟩
    iexists r
    iframe

private theorem word_exitN (n : Int) (j : w64) (Hj : 0 ≤ sint.Z j ∧ sint.Z j ≤ n)
    (Hif : ¬ sint.Z j < sint.Z (W64 n)) (hn : 0 ≤ n ∧ n < 2 ^ 63) : sint.Z j = n := by
  have : sint.Z (W64 n) = n := by word
  omega

private theorem word_stepN (n : Int) (j : w64) (Hj : 0 ≤ sint.Z j ∧ sint.Z j ≤ n)
    (Hif : sint.Z j < sint.Z (W64 n)) (hn : 0 ≤ n ∧ n < 2 ^ 63) :
    (0 ≤ sint.Z j ∧ sint.Z j < n) ∧ (0 ≤ sint.Z (j + W64 1) ∧ sint.Z (j + W64 1) ≤ n) := by
  have : sint.Z (W64 n) = n := by word
  refine ⟨⟨Hj.1, by omega⟩, ?_⟩
  have : sint.Z (j + W64 1) = sint.Z j + 1 := by word
  omega

private theorem arr_lookup {n : Int} (a : GoArray w64 n) (i : Int) (hl : (a.arr.length : Int) = n)
    (hi : 0 ≤ i ∧ i < n) : ∃ v, a.arr[i.toNat]? = some v :=
  ⟨_, List.getElem?_eq_getElem (by omega)⟩

theorem GetStatus.wp_proof (wp_getUint64 : getUint64.specAny (GF := GF) (hG := hG))
    (wp_getConfState : getConfState.specAny (GF := GF) (hG := hG))
    (wp_getMap : getMap.specAny (GF := GF) (hG := hG)) :
    GetStatus.spec (GF := GF) (hG := hG) := by
  intro b dq bs
  wp_start as Hb
  try wp_auto
  wp_apply wp_getUint64 b dq bs $$ [$Hb] as %ix %r1 %ok1 H1
  icases getUint64_post_any _ _ _ _ _ $$ H1 with ⟨%b1, Hr1⟩
  try wp_auto
  wp_apply wp_getConfState r1 dq b1 $$ [$Hr1] as %cs %r2 %ok2 H2
  icases getConfState_post_any _ _ _ _ $$ H2 with ⟨%b2, Hr2, Hcs⟩
  try wp_auto
  wp_apply wp_getMap r2 dq b2 $$ [$Hr2] as %mK %r3 %ok3 H3
  try wp_auto
  cases ok1 <;> cases ok2 <;> cases ok3
  all_goals try wp_auto
  all_goals try (iapply HΦ; simp only [Bool.false_eq_true, ↓reduceIte]; itrivial)
  simp only [↓reduceIte]
  icases Hcs with ⟨%c, Hcs⟩
  icases H3 with ⟨%K, %b3, HK, Hr3, -⟩
  try wp_auto
  rename_i ip0
  ihave IF : iprop(∃ (j : w64) (k0 : w64) (fa : GoArray w64 5) (rv : GoSlice) (bsr : List w8),
      "i" ∷ i_ptr ↦ j ∗ "iv" ∷ ip0 ↦ k0 ∗ "f" ∷ f_ptr ↦ fa ∗ "rest" ∷ rest_ptr ↦ rv ∗
      "Hrv" ∷ rv ↦*{dq} bsr ∗ "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ 5⌝)
    $$ [-HΦ «$res0» «$res1» s Hcs HK]
  · iexists W64 0, _, _, r3, b3
    iframe
    ipureintro; decide
  wp_for IF
  wp_if_destruct
  · obtain ⟨Hjr, Hj1⟩ := word_stepN 5 j Hj (by simpa using Hif) (by decide)
    try wp_auto
    wp_apply wp_getUint64 rv dq bsr $$ [$Hrv] as %x %r %ok Hr
    icases getUint64_post_any _ _ _ _ _ $$ Hr with ⟨%br, Hr⟩
    cases ok with
    | false =>
      try wp_auto
      wp_for_post
      iapply HΦ
      simp only [Bool.false_eq_true, ↓reduceIte]
      itrivial
    | true =>
    try wp_auto
    rw [ite_eq_left Hjr]
    ihave %Hfl := array_len _ _ _ _ $$ f
    obtain ⟨v, Hlk⟩ := arr_lookup fa (sint.Z j) (by omega) Hjr
    icases array_acc f_ptr (sint.Z j) (DFrac.own 1) 5 _ v Hjr.1 Hlk $$ f with ⟨Hfe, Hfb⟩
    try wp_auto
    ihave f := Hfb $$ %x Hfe
    try wp_auto
    wp_for_post
    iframe
    iexists j + W64 1, j, _, r, br
    iframe
    ipureintro; exact Hj1
  ihave %Hfl := array_len _ _ _ _ $$ f
  obtain ⟨fl⟩ := fa
  rcases fl with _ | ⟨a0, _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, _ | ⟨a4, _ | ⟨a5, t⟩⟩⟩⟩⟩⟩ <;>
    simp at Hfl <;> try omega
  icases typedPointsto_split _ _ _ $$ f with Hf
  simp only [TypedPointsto.typedPointstoDef]
  icases Hf with ⟨-, Hf⟩
  simp only [arrayElems]
  icases Hf with ⟨F0, F1, F2, F3, F4, -⟩
  rw [show ((0 : Nat) : Int) = sint.Z (W64 0) from rfl,
    show ((0 + 1 : Nat) : Int) = sint.Z (W64 1) from rfl,
    show ((0 + 1 + 1 : Nat) : Int) = sint.Z (W64 2) from rfl,
    show ((0 + 1 + 1 + 1 : Nat) : Int) = sint.Z (W64 3) from rfl,
    show ((0 + 1 + 1 + 1 + 1 : Nat) : Int) = sint.Z (W64 4) from rfl]
  try wp_auto
  ihave Hs : iprop(∃ sv : github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Status,
      s_ptr ↦ sv ∗ ⌜sv.Conf' = cs⌝) $$ [s]
  · iexists _; iframe; ipureintro; rfl
  icases Hs with ⟨%sv, s, %Hsv⟩
  by_cases ha : ¬ a4 = W64 numStats
  · rw [decide_eq_false ha]
    try wp_auto
    iapply HΦ
    simp only [Bool.false_eq_true, ↓reduceIte]
    itrivial
  rw [decide_eq_true (Classical.not_not.mp ha)]
  try wp_auto
  icases typedPointsto_not_null_dup _ _ _ $$ s with ⟨s, %Hsnn⟩
  icases typedPointsto_split _ _ _ $$ s with Hs
  simp only [TypedPointsto.typedPointstoDef]
  icases Hs with ⟨SI, SC, SCo, SL, ST, SR, SCm, SS⟩
  rename_i ip1
  icases SS with ⟨SS, -⟩
  ihave IS : iprop(∃ (j : w64) (k0 : w64) (sa : GoArray w64 numStats) (rv : GoSlice) (bsr : List w8),
      "i" ∷ i_ptr ↦ j ∗ "iv" ∷ ip1 ↦ k0 ∗
      "SS" ∷ s_ptr.[github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Status, go!"Stats"] ↦ sa ∗
      "rest" ∷ rest_ptr ↦ rv ∗
      "Hrv" ∷ rv ↦*{dq} bsr ∗ "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ numStats⌝)
    $$ [-HΦ «$res0» «$res1» Hcs HK SI SC SCo SL ST SR SCm F0 F1 F2 F3 F4 iv]
  · iexists W64 0, _, _, rv, bsr
    iframe
    ipureintro; decide
  wp_for IS
  wp_if_destruct
  · obtain ⟨Hjr, Hj1⟩ := word_stepN numStats j Hj (by simpa using Hif) (by decide)
    try wp_auto
    wp_apply wp_getUint64 rv dq bsr $$ [$Hrv] as %x %r %ok Hr
    icases getUint64_post_any _ _ _ _ _ $$ Hr with ⟨%br, Hr⟩
    cases ok with
    | false =>
      ihave s := typedPointsto_combine s_ptr ({ sv with Stats' := sa } :
          github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Status) (DFrac.own 1) Hsnn
        $$ [SI SC SCo SL ST SR SCm SS]
      · simp only [TypedPointsto.typedPointstoDef]; iframe
      try wp_auto
      wp_for_post
      iapply HΦ
      simp only [Bool.false_eq_true, ↓reduceIte]
      itrivial
    | true =>
    try wp_auto
    rw [ite_eq_left Hjr]
    ihave %Hfl := array_len _ _ _ _ $$ SS
    obtain ⟨v, Hlk⟩ := arr_lookup sa (sint.Z j) (by omega) Hjr
    icases array_acc _ (sint.Z j) (DFrac.own 1) numStats _ v Hjr.1 Hlk $$ SS with ⟨Hfe, Hfb⟩
    try wp_auto
    ihave SS := Hfb $$ %x Hfe
    try wp_auto
    wp_for_post
    iframe
    iexists j + W64 1, j, _, r, br
    iframe
    ipureintro; exact Hj1
  ihave s := typedPointsto_combine s_ptr ({ sv with Stats' := sa } :
      github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Status) (DFrac.own 1) Hsnn
    $$ [SI SC SCo SL ST SR SCm SS]
  · simp only [TypedPointsto.typedPointstoDef]; iframe
  try wp_auto
  iapply HΦ
  split
  · iexists c
    simp only [Hsv]
    iexact Hcs
  · itrivial

end proof

end kvraft
end EtcdGrove
end Perennial

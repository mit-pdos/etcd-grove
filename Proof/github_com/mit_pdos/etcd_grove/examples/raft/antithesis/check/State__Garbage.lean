/-
Lean-first (no Rocq counterpart). #33 S3b W6 (2026-11-23): the proof of `State.Garbage` (B 696-706).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State__Garbage
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State__idx
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State__EffTerm
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State__Over
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.factsHas
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.StateLaws
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.EvalLaws
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.ActionLaws
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.W6Laws

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntCheck

open Iris Iris.BI Iris.ProofMode

section proof
set_option linter.unusedSimpArgs false
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Assumptions]

set_option hygiene false in
/-- The end of `Garbage`'s outer loop body, `m` kept (`g` true). -/
local macro "gtail_t" : tactic => `(tactic| (
  (try wp_auto); wp_apply wp_slice_literal; isplitr; (ipureintro; rfl);
  iintro %sl1 ⟨Hsl1, -⟩;
  wp_apply wp_slice_append $$ [Hout Hcap Hsl1] as %s1 ⟨Hs1, Hcap1, -⟩; (iframe);
  (try wp_auto); wp_for_post; iframe; iexists _, _, _, _, _; iframe; ipureintro;
  refine ⟨by omega, by omega, W6Laws.forall₂_append_one hkL hrz, ?_⟩;
  rw [hk1']; simpa using hkS))

set_option hygiene false in
/-- The end of `Garbage`'s inner loop body, `a` not a later ack (`c1` false). -/
local macro "itail_f" : tactic => `(tactic| (
  subst hc1; (try wp_auto); wp_for_post; iframe; iexists _, _; iframe; ipureintro;
  refine ⟨by omega, by omega, ?_⟩;
  rw [hj1']; simpa using hjS))

set_option hygiene false in
/-- The end of `Garbage`'s outer loop body, `m` dropped (`g` false). -/
local macro "gtail_f" : tactic => `(tactic| (
  (try wp_auto); wp_for_post; iframe; iexists _, _, _, _, _; iframe; ipureintro;
  refine ⟨by omega, by omega, hkL, ?_⟩;
  rw [hk1']; simpa using hkS))

theorem State.Garbage.wp_proof
    (wp_idx : State.idx.spec (GF := GF) (hG := hG))
    (wp_EffTerm : State.EffTerm.spec (GF := GF) (hG := hG))
    (wp_Over : State.Over.spec (GF := GF) (hG := hG))
    (wp_factsHas : factsHas.spec (GF := GF) (hG := hG)) :
    State.Garbage.spec (GF := GF) (hG := hG) := by
  intro p s gs
  wp_start as ⟨#Hs, %Ho⟩
  ihave #Hs' := Hs
  iunfold stateRO at Hs'
  iNamed Hs'
  iNamed Hf
  iStructNamed Hp
  ihave #Hv := HMsgs
  iunfold factsRO at Hv
  icases Hv with ⟨%items, #Hitems, %Hrel⟩
  ihave %Hil := ownSlice_len $$ Hitems
  have Hl := Hrel.length_eq
  rw [State.garbage, W6Laws.filterM_eq] at Ho
  generalize hF : (fun m : Fact => _) = F at Ho
  iapply wp_fupd
  wp_auto
  have hvl : sint.nat g.Msgs'.len = items.length := by rw [Hil.1]
  ihave #Hnil := ownSlice_nil (V := G.Fact) (GF := GF) (DFrac.own 1)
  ihave Hcap0 := ownSliceCap_nil (V := G.Fact) (GF := GF)
  ihave IH : iprop(∃ (k : w64) (vv : G.Fact) (osl : GoSlice) (L : List G.Fact) (acc : List Fact),
      "i" ∷ i_ptr ↦ k ∗ "m" ∷ m_ptr ↦ vv ∗ "out" ∷ out_ptr ↦ osl ∗ "Hout" ∷ osl ↦* L ∗
      "Hcap" ∷ ownSliceCap G.Fact osl (DFrac.own 1) ∗
      "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ sint.Z g.Msgs'.len ∧ List.Forall₂ factRel L acc ∧
        (s.msgs.drop (sint.nat k)).foldlM (W6Laws.fstep F) acc = .ok gs⌝) $$ [i m out Hcap0]
  · iexists _, _, slice.nil, [], []
    iframe
    isplitr
    · iexact Hnil
    isplitr
    · iexact Hcap0
    ipureintro
    exact ⟨Int.le_refl _, Hil.2, .nil, by rw [show sint.nat (W64 0) = 0 from rfl]; simpa using Ho⟩
  wp_for IH
  obtain ⟨hk0, hk1, hkL, hkS⟩ := Hk
  wp_if_destruct
  · have Hlt' : sint.nat k < items.length := by rw [← hvl]; have := sint_nat_cast hk0; have := sint_nat_cast Hil.2; omega
    have Hltv : sint.nat k < s.msgs.length := by omega
    obtain ⟨z, Hz⟩ : ∃ z, items[sint.nat k]? = some z := ⟨_, List.getElem?_eq_getElem Hlt'⟩
    have hrz : factRel z s.msgs[sint.nat k] := by
      have := forall₂_getElem Hrel (sint.nat k) Hlt' Hltv
      rw [List.getElem?_eq_getElem Hlt'] at Hz; cases Hz; exact this
    obtain ⟨c, hc, hkS⟩ := W6Laws.fold_step Hltv hkS
    rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z k ∧ sint.Z k < sint.Z g.Msgs'.len from ⟨hk0, Hif⟩))]
    wp_apply wp_load_slice_index g.Msgs' (sint.Z k) items DFrac.discard z hk0 $$ [Hitems] as -
    · isplitr
      · iexact Hitems
      ipureintro; rw [show (sint.Z k).toNat = sint.nat k by rfl]; exact Hz
    try wp_auto
    have hk1' : sint.nat (k + W64 1) = sint.nat k + 1 := by
      have := sint_add_one_lt Hif; have := sint_nat_cast hk0
      have := sint_nat_cast (k := k + W64 1) (by omega); omega
    have hk' := sint_add_one_lt Hif
    rw [← hF] at hc
    simp only at hc
    rw [hrz.1]
    by_cases hv : s.msgs[sint.nat k].type = go!"vote"
    · rw [decide_eq_true hv]
      rw [beq_of_eq' hv] at hc
      simp only [ite_true, pure_ok, Except.ok.injEq] at hc
      try wp_auto
      wp_apply wp_Over p s z.Term' $$ [Hs]
      · iexact Hs
      rw [hrz.2.2.2.1, hc]
      try wp_auto
      cases c
      · gtail_f
      · gtail_t
    rw [decide_eq_false hv]
    rw [beq_of_ne' hv] at hc
    simp only [Bool.false_eq_true, ite_false] at hc
    try wp_auto
    rw [hrz.1]
    by_cases hg : s.msgs[sint.nat k].type = go!"grant"
    · rw [decide_eq_true hg]
      rw [beq_of_eq' hg] at hc
      simp only [ite_true] at hc
      obtain ⟨j, hj, hc⟩ := bind_ok hc
      simp only [pure_ok, Except.ok.injEq] at hc
      try wp_auto
      wp_apply wp_idx p s z.Dst' j $$ [Hs] as %w %Hw
      · iframe Hs; ipureintro; rw [hrz.2.2.1]; exact hj
      try wp_auto
      wp_apply wp_EffTerm p s w $$ [Hs] as %u %Hu
      · iframe Hs; ipureintro; omega
      try wp_auto
      have hwn : sint.nat w = j := by have := sint_nat_cast (k := w) (by omega); omega
      rw [Hu, hrz.2.2.2.1, hwn, hc]
      try wp_auto
      cases c
      · gtail_f
      · gtail_t
    rw [decide_eq_false hg]
    rw [beq_of_ne' hg] at hc
    simp only [Bool.false_eq_true, ite_false] at hc
    try wp_auto
    rw [hrz.1]
    by_cases ha : s.msgs[sint.nat k].type = go!"ack"
    case neg =>
      rw [decide_eq_false ha]
      rw [beq_of_ne' ha] at hc
      simp only [Bool.false_eq_true, ite_false, pure_ok, Except.ok.injEq] at hc
      subst hc
      gtail_f
    rw [decide_eq_true ha]
    rw [beq_of_eq' ha] at hc
    simp only [ite_true] at hc
    obtain ⟨j, hj, hc⟩ := bind_ok hc
    try wp_auto
    wp_apply wp_idx p s z.Dst' j $$ [Hs] as %w %Hw
    · iframe Hs; ipureintro; rw [hrz.2.2.1]; exact hj
    try wp_auto
    wp_apply wp_EffTerm p s w $$ [Hs] as %u %Hu
    · iframe Hs; ipureintro; omega
    try wp_auto
    have hwn : sint.nat w = j := by have := sint_nat_cast (k := w) (by omega); omega
    rw [Hu, hrz.2.2.2.1, hwn]
    by_cases he : s.effTerm j > s.msgs[sint.nat k].term
    · rw [decide_eq_true he]
      rw [decide_eq_true he] at hc
      simp only [ite_true, pure_ok, Except.ok.injEq] at hc
      subst hc
      gtail_t
    rw [decide_eq_false he]
    rw [decide_eq_false he] at hc
    simp only [Bool.false_eq_true, ite_false] at hc
    generalize hG : (fun a : Fact => _) = Fa at hc
    try wp_auto
    ihave IH2 : iprop(∃ (j2 : w64) (aa : G.Fact),
        "i" ∷ i_ptr ↦ j2 ∗ "a" ∷ a_ptr ↦ aa ∗ "g" ∷ g_ptr ↦ false ∗
        "%Hj" ∷ ⌜0 ≤ sint.Z j2 ∧ sint.Z j2 ≤ sint.Z g.Msgs'.len ∧
          anyM (s.msgs.drop (sint.nat j2)) Fa = .ok c⌝) $$ [i a g]
    · iexists _, _
      iframe
      ipureintro
      exact ⟨Int.le_refl _, Hil.2, by rw [show sint.nat (W64 0) = 0 from rfl]; simpa using hc⟩
    wp_for IH2
    obtain ⟨hj0, hj1, hjS⟩ := Hj
    wp_if_destruct
    · have Hlt2 : sint.nat j2 < items.length := by rw [← hvl]; have := sint_nat_cast hj0; have := sint_nat_cast Hil.2; omega
      have Hltv2 : sint.nat j2 < s.msgs.length := by omega
      obtain ⟨z2, Hz2⟩ : ∃ z, items[sint.nat j2]? = some z := ⟨_, List.getElem?_eq_getElem Hlt2⟩
      have hrz2 : factRel z2 s.msgs[sint.nat j2] := by
        have := forall₂_getElem Hrel (sint.nat j2) Hlt2 Hltv2
        rw [List.getElem?_eq_getElem Hlt2] at Hz2; cases Hz2; exact this
      rw [List.drop_eq_getElem_cons Hltv2, anyM_cons] at hjS
      obtain ⟨c1, hc1, hjS⟩ := bind_ok hjS
      rw [← hG] at hc1
      simp only at hc1
      rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z j2 ∧ sint.Z j2 < sint.Z g.Msgs'.len from ⟨hj0, Hif⟩))]
      wp_apply wp_load_slice_index g.Msgs' (sint.Z j2) items DFrac.discard z2 hj0 $$ [Hitems] as -
      · isplitr
        · iexact Hitems
        ipureintro; rw [show (sint.Z j2).toNat = sint.nat j2 by rfl]; exact Hz2
      try wp_auto
      have hj1' : sint.nat (j2 + W64 1) = sint.nat j2 + 1 := by
        have := sint_add_one_lt Hif; have := sint_nat_cast hj0
        have := sint_nat_cast (k := j2 + W64 1) (by omega); omega
      have hj' := sint_add_one_lt Hif
      rw [hrz2.1]
      by_cases h1 : s.msgs[sint.nat j2].type = go!"ack"
      case neg =>
        rw [decide_eq_false h1]
        simp [beq_of_ne' h1] at hc1
        itail_f
      rw [decide_eq_true h1]
      try wp_auto
      rw [hrz2.2.1, hrz.2.1]
      by_cases h2 : s.msgs[sint.nat j2].src = s.msgs[sint.nat k].src
      case neg =>
        rw [decide_eq_false h2]
        simp [beq_of_ne' h2] at hc1
        itail_f
      rw [decide_eq_true h2]
      try wp_auto
      rw [hrz2.2.2.1, hrz.2.2.1]
      by_cases h3 : s.msgs[sint.nat j2].dst = s.msgs[sint.nat k].dst
      case neg =>
        rw [decide_eq_false h3]
        simp [beq_of_ne' h3] at hc1
        itail_f
      rw [decide_eq_true h3]
      try wp_auto
      rw [decide_w64_eq, hrz2.2.2.2.1, hrz.2.2.2.1]
      by_cases h4 : s.msgs[sint.nat j2].term = s.msgs[sint.nat k].term
      case neg =>
        rw [decide_eq_false h4]
        simp [beq_of_ne' h4] at hc1
        itail_f
      rw [decide_eq_true h4]
      try wp_auto
      rw [hrz2.2.2.2.2.2.2, hrz.2.2.2.2.2.2]
      by_cases h5 : s.msgs[sint.nat j2].index > s.msgs[sint.nat k].index
      case neg =>
        rw [decide_eq_false h5]
        simp [h5] at hc1
        itail_f
      rw [decide_eq_true h5]
      simp [h1, h2, h3, h4, h5] at hc1
      obtain ⟨j3, hj3, hc1⟩ := bind_ok hc1
      try wp_auto
      wp_apply wp_idx p s z2.Src' j3 $$ [Hs] as %w3 %Hw3
      · iframe Hs; ipureintro; rw [hrz2.2.1, h2]; exact hj3
      have hwn3 : sint.nat w3 = j3 := by have := sint_nat_cast (k := w3) (by omega); omega
      icases undoRO_at g.Undo' s.undo w3 ⟨by omega, by rw [HWf.len_undo]; omega⟩ $$ HUndo with ⟨%v, #Hua, #Hpu⟩
      try wp_auto
      wp_apply wp_load_at _ _ v (by omega) $$ [Hua]
      · iexact Hua
      try wp_auto
      rw [← List.getElem!_eq_getElem?_getD, ← hwn3] at hc1
      cases hu : s.undo[sint.nat w3]! with
      | none =>
        rw [hu] at hc1
        simp only [Except.ok.injEq] at hc1
        subst hc1
        simp only [ite_true, pure_ok, Except.ok.injEq] at hjS
        subst hjS
        iunfold preRO at Hpu
        icases Hpu with %Hnull
        subst Hnull
        try wp_auto
        wp_for_post
        gtail_t
      | some pu =>
        rw [hu] at hc1
        simp only [Except.ok.injEq] at hc1
        iunfold preRO at Hpu
        icases Hpu with ⟨%gp, #Hgp, %Hpf, #Hsuf, #Hms, #Hvs, #Hacks⟩
        ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hgp
        ihave #Hgp' := Hgp
        iStructNamed Hgp'
        wp_if_destruct
        · exact absurd rfl Hnn
        try wp_auto
        wp_apply wp_factsHas gp.Msgs' pu.msgs z2 s.msgs[sint.nat j2] $$ [Hms]
        · iframe Hms; ipureintro; exact hrz2
        cases hcon : pu.msgs.contains s.msgs[sint.nat j2]
        · have hcon' := hcon
          simp at hcon'
          simp [hcon'] at hc1
          subst hc1
          simp only [ite_true, pure_ok, Except.ok.injEq] at hjS
          subst hjS
          try wp_auto
          wp_for_post
          gtail_t
        · have hcon' := hcon
          simp at hcon'
          simp [hcon'] at hc1
          itail_f
    have hjn : sint.nat j2 = s.msgs.length := by
      rw [← Hl, ← hvl]; have := sint_nat_cast hj0; have := sint_nat_cast Hil.2; omega
    rw [hjn, List.drop_length] at hjS
    simp only [anyM, pure_ok, Except.ok.injEq] at hjS
    subst hjS
    try wp_auto
    gtail_f
  have hkn : sint.nat k = s.msgs.length := by
    rw [← Hl, ← hvl]; have := sint_nat_cast hk0; have := sint_nat_cast Hil.2; omega
  rw [hkn] at hkS
  have hacc := W6Laws.fold_end hkS
  subst hacc
  try wp_auto
  imod ownSlice_persist $$ Hout with #Hout
  imodintro
  iapply HΦ
  iunfold factsRO
  iexists _
  iframe Hout
  ipureintro; exact hkL

end proof

end AntCheck
end EtcdGrove
end Perennial

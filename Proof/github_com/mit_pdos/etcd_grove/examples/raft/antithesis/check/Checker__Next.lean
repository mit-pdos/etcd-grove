/-
Lean-first (no Rocq counterpart). #33 S3b W7 (2026-11-23): the proof of `Checker.Next` (`check.go`).

`violated`'s result is compared with `nil` (`v != nil`), and `violated.spec` does not say that an
empty result is `nil`; the call is proved here by the triple `Checker.Next.violated_wp` (`violated`'s
proof, its postcondition with the fact), over `ElectionSafety`'s and `OneVotePerTerm`'s specs.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Checker__Next
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State__ElectionSafety
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State__OneVotePerTerm
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State__GCDue
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State__GC
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State__Step
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.StateLaws
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.EvalLaws
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Init0Laws
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.CheckLaws

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

/-- `violated`, with the fact `Next` compares its result by: an empty result is `nil`. -/
theorem Checker.Next.violated_wp
    (wp_ElectionSafety : State.ElectionSafety.spec (GF := GF) (hG := hG))
    (wp_OneVotePerTerm : State.OneVotePerTerm.spec (GF := GF) (hG := hG)) :
  ∀ (p : Loc) (s : State),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check ∗
      stateRO p s }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.violated)) (Val #p))
  {{ (u : GoSlice), RET #u; strsRO u (violated s) ∗ ⌜violated s = [] → u = slice.nil⌝ }} := by
  intro p s
  wp_start as #Hs
  iapply wp_fupd
  ihave #Hs' := Hs
  iunfold stateRO at Hs'
  iNamed Hs'
  iNamed Hf
  iStructNamed Hp
  wp_auto
  wp_apply wp_ElectionSafety p s $$ [Hs]
  · iexact Hs
  try wp_auto
  cases hES : s.electionSafety
  · try wp_auto
    wp_apply wp_slice_literal (V := GoString) [go!"ElectionSafety"]
    isplitr
    · ipureintro; rfl
    iintro %sl ⟨Hsl, -⟩
    wp_auto
    ipersist Hsl
    iapply HΦ
    unfold violated; simp only [hES, Bool.not_false, ↓reduceIte]
    imodintro; iunfold strsRO; iframe Hsl; ipureintro; intro h; cases h
  try wp_auto
  wp_apply wp_OneVotePerTerm p s $$ [Hs]
  · iexact Hs
  try wp_auto
  cases hOV : s.oneVotePerTerm
  · try wp_auto
    wp_apply wp_slice_literal (V := GoString) [go!"OneVotePerTerm"]
    isplitr
    · ipureintro; rfl
    iintro %sl ⟨Hsl, -⟩
    wp_auto
    ipersist Hsl
    iapply HΦ
    unfold violated; simp only [hES, hOV, Bool.not_true, Bool.not_false, Bool.false_eq_true, ↓reduceIte]
    imodintro; iunfold strsRO; iframe Hsl; ipureintro; intro h; cases h
  try wp_auto
  ihave %Hvl := strsRO_len _ _ $$ HViol
  have hv : violated s = s.viol := by
    unfold violated; simp only [hES, hOV, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rw [hv]
  try wp_auto
  by_cases h0 : g.Viol'.len = W64 0
  · rw [decide_eq_true h0]
    have hnil : s.viol = [] := by
      rw [h0, sint_zero] at Hvl; exact List.eq_nil_of_length_eq_zero (by omega)
    try wp_auto
    iapply HΦ
    rw [hnil]
    imodintro
    iframe; isplitl
    · iapply Init0_strsNil
    · ipureintro; intro _; rfl
  · rw [decide_eq_false h0]
    try wp_auto
    iapply HΦ
    imodintro
    iframe HViol
    ipureintro; intro hn; rw [hn] at Hvl; exfalso; apply h0; simp at Hvl; word


theorem Checker.Next.wp_proof
    (wp_ElectionSafety : State.ElectionSafety.spec (GF := GF) (hG := hG))
    (wp_OneVotePerTerm : State.OneVotePerTerm.spec (GF := GF) (hG := hG))
    (wp_GCDue : State.GCDue.spec (GF := GF) (hG := hG))
    (wp_GC : State.GC.spec (GF := GF) (hG := hG))
    (wp_Step : State.Step.spec (GF := GF) (hG := hG))
    (gc_within : GCWithin) :
    Checker.Next.spec (GF := GF) (hG := hG) := by
  have wp_violated := Checker.Next.violated_wp wp_ElectionSafety wp_OneVotePerTerm
  intro p c e ev c'
  wp_start as ⟨Hc, #He, %Hb, %Hn⟩
  iunfold checkerOwn at Hc
  icases Hc with ⟨%g, Hp, #Hs, #Hv, %Hd⟩
  obtain ⟨gs, gd, gv⟩ := g
  simp only at Hd
  subst Hd
  icases typedPointsto_not_null_dup _ _ _ $$ Hp with ⟨Hp, %Hpn⟩
  icases typedPointsto_split _ _ _ $$ Hp with Hp
  simp only [TypedPointsto.typedPointstoDef, named]
  icases Hp with ⟨State, Done, Verdict, -⟩
  wp_auto
  cases hd : c.done
  case true =>
    have hc' := CheckLaws.next_of_done ev hd
    rw [hc'] at Hn; cases Hn
    wp_pures
    try wp_auto
    iapply HΦ
    iunfold checkerOwn
    iexists { State' := gs, Done' := c.done, Verdict' := gv }
    simp only [hd]
    isplitl [State Done Verdict]
    · iapply typedPointsto_combine _ _ _ Hpn
      simp only [TypedPointsto.typedPointstoDef, named]
      iframe
    iframe Hs Hv
  obtain ⟨b, E, hW, hNO, hCh, hb, hcf⟩ := Hb hd
  obtain ⟨sF, vo, hg, hsome, hnone⟩ := CheckLaws.next_ok hd Hn
  wp_pures
  wp_auto
  ihave IH : iprop(∃ (sp : Loc) (s0 : State) (k : Nat),
      "s" ∷ s_ptr ↦ sp ∗ "Hs0" ∷ stateRO sp s0 ∗
      "%Hk" ∷ ⌜gcLoop k s0 = .ok (sF, vo) ∧ s0.Within b E⌝) $$ [s]
  · iexists _, _, _
    iframe s Hs
    ipureintro; exact ⟨hg, hW⟩
  wp_for_core
  icases IH with ⟨%sp, %s0, %k, Hsv, #Hs0, %Hk⟩
  iNamed Hsv
  iNamed Hs0
  try wp_auto
  obtain ⟨hk, hWs0⟩ := Hk
  obtain ⟨k', -, due, hdue, hf, ht⟩ := CheckLaws.gcLoop_ok hk
  have hbN : (b : Int) < numBound := by
    have : (b : Int) ≤ ((b + ev.weight : Nat) : Int) := by omega
    omega
  wp_apply wp_GCDue sp s0 due $$ [Hs0]
  · iframe Hs0; ipureintro; exact ⟨⟨b, E, hbN, hWs0⟩, hdue⟩
  cases due
  case false =>
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (hf rfl)
    cleanup_bool_decide
    try wp_auto
    obtain ⟨o, hso, hno, hsome'⟩ := hnone rfl
    have hcfg := CheckLaws.gcLoop_cfg _ _ _ _ hg
    have hBF : sF.BoundedFor ev := ⟨b, E, hWs0, hNO, hCh, hb, by rw [hcfg]; exact hcf⟩
    wp_apply wp_Step sp sF e ev o $$ [Hs0 He] as %q %ok Ho
    · iframe Hs0 He; ipureintro; exact ⟨hBF, hso⟩
    ihave #HsF := Hs0
    iunfold stateRO at HsF
    iNamed HsF
    iNamed Hf
    iStructNamedSuffix Hp "F"
    cases o with
    | none =>
      iunfold succOwn at Ho
      icases Ho with %Hok
      subst Hok
      have hc' := hno rfl
      subst hc'
      try wp_auto
      iapply HΦ
      iunfold checkerOwn
      iexists { State' := sp, Done' := true, Verdict' := { Kind' := W64 1, K' := g.I', Names' := slice.nil, Err' := [] } }
      isplitl [State Done Verdict]
      · iapply typedPointsto_combine _ _ _ Hpn
        simp only [TypedPointsto.typedPointstoDef, named]
        iframe
      iframe Hs0
      isplitl
      · iunfold verdictRO
        isplitr
        · ipureintro; exact ⟨rfl, HI, rfl⟩
        · iapply Init0_strsNil
      · ipureintro; rfl
    | some ns =>
      iunfold succOwn at Ho
      icases Ho with ⟨%Hok, Hq⟩
      subst Hok
      imod stateOwn_persist _ _ $$ Hq with #Hq
      obtain ⟨hv1, hv0⟩ := hsome' ns rfl
      try wp_auto
      wp_apply wp_violated q ns $$ [Hq] as %u ⟨#Hu, %Hnil⟩
      · iexact Hq
      try wp_auto
      by_cases h0 : violated ns = []
      · rw [decide_eq_true (Hnil h0)]
        have hc' := hv0 h0
        subst hc'
        try wp_auto
        iapply HΦ
        iunfold checkerOwn
        iexists { State' := q, Done' := false, Verdict' := gv }
        isplitl [State Done Verdict]
        · iapply typedPointsto_combine _ _ _ Hpn
          simp only [TypedPointsto.typedPointstoDef, named]
          iframe
        simp only [hd]
        iframe Hq Hv
      · ihave %Hul := strsRO_len _ _ $$ Hu
        have hun : u ≠ slice.nil := by
          intro h; subst h; apply h0
          exact List.eq_nil_of_length_eq_zero (by simp [slice.nil] at Hul; omega)
        rw [decide_eq_false hun]
        have hc' := hv1 h0
        subst hc'
        try wp_auto
        iapply HΦ
        iunfold checkerOwn
        iexists { State' := q, Done' := true, Verdict' := { Kind' := W64 2, K' := g.I', Names' := u, Err' := [] } }
        isplitl [State Done Verdict]
        · iapply typedPointsto_combine _ _ _ Hpn
          simp only [TypedPointsto.typedPointstoDef, named]
          iframe
        iframe Hq
        isplitl
        · iunfold verdictRO
          isplitr
          · ipureintro; exact ⟨rfl, HI, rfl⟩
          · iexact Hu
        · ipureintro; rfl
  case true =>
    obtain ⟨s1, hg1, hv1, hn1⟩ := ht rfl
    cleanup_bool_decide
    try wp_auto
    wp_apply wp_GC sp s0 s1 $$ [Hs0] as %q1 Hq1
    · iframe Hs0; ipureintro; exact hg1
    imod stateOwn_persist _ _ $$ Hq1 with #Hq1
    have hW1 := gc_within _ _ _ _ hWs0 hg1
    try wp_auto
    wp_apply wp_violated q1 s1 $$ [Hq1] as %u ⟨#Hu, %Hnil⟩
    · iexact Hq1
    try wp_auto
    by_cases h0 : violated s1 = []
    · rw [decide_eq_true (Hnil h0)]
      try wp_auto
      wp_for_post
      iframe HΦ State Done Verdict c ev
      iexists q1, s1, k'
      iframe s Hq1
      ipureintro; exact ⟨hn1 h0, hW1⟩
    · ihave %Hul := strsRO_len _ _ $$ Hu
      have hun : u ≠ slice.nil := by
        intro h; subst h; apply h0
        exact List.eq_nil_of_length_eq_zero (by simp [slice.nil] at Hul; omega)
      rw [decide_eq_false hun]
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (hv1 h0)
      have hc' := hsome _ rfl
      subst hc'
      ihave #Hq1' := Hq1
      iunfold stateRO at Hq1'
      iNamed Hq1'
      iNamed Hf
      iStructNamedSuffix Hp "1"
      have hi1 := hW1.2.1
      try wp_auto
      wp_for_post
      iapply HΦ
      iunfold checkerOwn
      iexists { State' := q1, Done' := true, Verdict' := { Kind' := W64 2, K' := g.I' - W64 1, Names' := u, Err' := [] } }
      isplitl [State Done Verdict]
      · iapply typedPointsto_combine _ _ _ Hpn
        simp only [TypedPointsto.typedPointstoDef, named]
        iframe
      iframe Hq1
      isplitl
      · iunfold verdictRO
        isplitr
        · ipureintro; exact ⟨rfl, by rw [sint_sub_one (by omega), HI], rfl⟩
        · iexact Hu
      · ipureintro; rfl

end proof

end AntCheck
end EtcdGrove
end Perennial

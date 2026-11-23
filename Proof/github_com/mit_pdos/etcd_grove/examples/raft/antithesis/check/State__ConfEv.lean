/-
Lean-first (no Rocq counterpart). #33 S3b W2 (2026-11-23): the proof of `State.ConfEv` (B 614-630).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State__ConfEv
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State__clone
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Event__index
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.SubSeq
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.EntriesEqual
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.At
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.IsConf
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Legal
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.RecordedIn
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.NextConf
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.SameConf
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.setConf
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.setInt
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.TermConfs__With
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.TermInts__With
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.StateLaws
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.EvalLaws
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.ActionLaws
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Within.Parts

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

theorem State.ConfEv.wp_proof
    (wp_clone : State.clone.spec (GF := GF) (hG := hG))
    (wp_index : Event.index.spec (GF := GF) (hG := hG))
    (wp_SubSeq : SubSeq.spec (GF := GF) (hG := hG))
    (wp_EntriesEqual : EntriesEqual.spec (GF := GF) (hG := hG))
    (wp_At : At.spec (GF := GF) (hG := hG))
    (wp_IsConf : IsConf.spec (GF := GF) (hG := hG))
    (wp_Legal : Legal.spec (GF := GF) (hG := hG))
    (wp_RecordedIn : RecordedIn.spec (GF := GF) (hG := hG))
    (wp_NextConf : NextConf.spec (GF := GF) (hG := hG))
    (wp_SameConf : SameConf.spec (GF := GF) (hG := hG))
    (wp_setConf : setConf.spec (GF := GF) (hG := hG))
    (wp_setInt : setInt.spec (GF := GF) (hG := hG))
    (wp_ConfWith : TermConfs.With.spec (GF := GF) (hG := hG))
    (wp_IntWith : TermInts.With.spec (GF := GF) (hG := hG)) :
    State.ConfEv.spec (GF := GF) (hG := hG) := by
  intro p s n e ev o
  wp_start as ⟨#Hs, #He, %Hn, %Hlt, %HBd, %Ho⟩
  ihave #Hs' := Hs
  iunfold stateRO at Hs'
  iNamed Hs'
  iNamed Hf
  iStructNamed Hp

  obtain ⟨bb, EE, HW, HNO, HCh, hbb, hEE⟩ := HBd
  unfold numBound Event.weight at hbb
  unfold State.confEv at Ho
  obtain ⟨k, hk, Ho⟩ := bind_ok Ho
  have hkn : numOk k := by have := HNO.2.2.2.2.2.2.2.2.1; rw [need_ok hk] at this; exact this
  unfold numOk numBound at hkn
  have hn' : sint.nat n < s.cfg.server.length := by have := sint_nat_cast Hn; omega
  icases logsRO_at g.Log' s.log n ⟨Hn, by rw [HWf.len_log]; exact Hlt⟩ $$ HLog with ⟨%lg, #Hlga, #Hlg⟩
  ihave %Hlgl := logRO_len _ _ $$ Hlg
  ihave %Hchl := logRO_len _ _ $$ HChain
  icases intsRO_at g.ConfAt' s.confAt n ⟨Hn, by rw [HWf.len_confAt]; exact Hlt⟩ $$ HConfAt with ⟨%ca, #Hcaa, %Hca⟩
  icases intsRO_at g.LastApplied' s.lastApplied n ⟨Hn, by rw [HWf.len_lastApplied]; exact Hlt⟩ $$ HLastApplied with ⟨%la, #Hlaa, %Hla⟩
  have hcab : bigOk s.confAt[sint.nat n]! := HW.confAt _ (getElem!_mem (by rw [HWf.len_confAt]; exact hn'))
  unfold bigOk at hcab
  wp_auto
  wp_apply wp_index e ev k $$ [He] as %uk %Huk
  · iframe He; ipureintro; exact hk
  try wp_auto
  wp_apply wp_load_at _ _ lg Hn $$ [Hlga]
  · iexact Hlga
  try wp_auto
  wp_apply wp_load_at _ _ ca Hn $$ [Hcaa]
  · iexact Hcaa
  try wp_auto
  rw [Huk, Hca]
  dsimp only at Ho
  by_cases h1 : s.confAt[sint.nat n]! < k ∧ k ≤ s.lastApplied[sint.nat n]! ∧ k ≤ (s.log[sint.nat n]!).length
  case neg =>
    have : (!(decide (k > s.confAt[sint.nat n]!) && decide (k ≤ s.lastApplied[sint.nat n]!) &&
        decide (k ≤ ↑(s.log[sint.nat n]!).length))) = true := by
      simp only [Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not, gt_iff_lt]; omega
    rw [this] at Ho
    simp only [ite_true, pure_ok, Except.ok.injEq] at Ho
    by_cases ha : s.confAt[sint.nat n]! < k
    · rw [decide_eq_true ha]
      try wp_auto
      wp_apply wp_load_at _ _ la Hn $$ [Hlaa]
      · iexact Hlaa
      try wp_auto
      rw [Huk, Hla]
      by_cases hb : k ≤ s.lastApplied[sint.nat n]!
      · rw [decide_eq_true hb]
        try wp_auto
        rw [Huk, Hlgl, decide_eq_false (by omega)]
        subst Ho
        try wp_auto
        iapply HΦ; iunfold succOwn; ipureintro; rfl
      · rw [decide_eq_false hb]
        subst Ho
        try wp_auto
        iapply HΦ; iunfold succOwn; ipureintro; rfl
    · rw [decide_eq_false ha]
      subst Ho
      try wp_auto
      iapply HΦ; iunfold succOwn; ipureintro; rfl
  rw [decide_eq_true h1.1]
  try wp_auto
  wp_apply wp_load_at _ _ la Hn $$ [Hlaa]
  · iexact Hlaa
  try wp_auto
  rw [Huk, Hla, decide_eq_true h1.2.1]
  try wp_auto
  rw [Huk, Hlgl, decide_eq_true h1.2.2]
  have : (!(decide (k > s.confAt[sint.nat n]!) && decide (k ≤ s.lastApplied[sint.nat n]!) &&
      decide (k ≤ ↑(s.log[sint.nat n]!).length))) = false := by
    simp only [Bool.not_eq_false', Bool.and_eq_true, decide_eq_true_eq, gt_iff_lt]; omega
  rw [this] at Ho
  simp only [Bool.false_eq_true, ite_false] at Ho
  -- `k <= len(s.Chain) && EntriesEqual(SubSeq(s.Chain, 1, k), SubSeq(logn, 1, k))`
  obtain ⟨c2, hc2, Ho⟩ := bind_ok Ho
  obtain ⟨x2, hx2, ht2, hf2⟩ := andM_ok hc2
  simp only [pure_ok, Except.ok.injEq] at hx2
  subst hx2
  try wp_auto
  rw [Huk, Hchl]
  by_cases h2 : k ≤ s.chain.length
  case neg =>
    rw [decide_eq_false h2]
    rw [hf2 (decide_eq_false h2)] at Ho
    simp only [Bool.not_false, ite_true, pure_ok, Except.ok.injEq] at Ho
    subst Ho
    try wp_auto
    iapply HΦ; iunfold succOwn; ipureintro; rfl
  rw [decide_eq_true h2]
  have hc2' := ht2 (decide_eq_true h2)
  obtain ⟨sc, hsc, hc2'⟩ := bind_ok hc2'
  obtain ⟨sl, hsl, hc2'⟩ := bind_ok hc2'
  try wp_auto
  wp_apply wp_SubSeq g.Chain' s.chain (W64 1) uk sc $$ [HChain] as %scl #Hsc
  · iframe HChain; ipureintro; rw [Huk, sint_one]; exact hsc
  try wp_auto
  wp_apply wp_SubSeq lg _ (W64 1) uk sl $$ [Hlg] as %sll #Hsl
  · iframe Hlg; ipureintro; rw [Huk, sint_one]; exact hsl
  try wp_auto
  wp_apply wp_EntriesEqual scl sc sll sl c2 $$ [Hsc Hsl]
  · iframe Hsc Hsl; ipureintro; exact hc2'
  cases c2
  · simp only [Bool.not_false, ite_true, pure_ok, Except.ok.injEq] at Ho
    subst Ho
    try wp_auto
    iapply HΦ; iunfold succOwn; ipureintro; rfl
  simp only [Bool.not_true, Bool.false_eq_true, ite_false] at Ho
  -- `IsConf(At(logn, k))`
  obtain ⟨en, he, Ho⟩ := bind_ok Ho
  have hem := atE_mem he
  have heb : en.chgSize ≤ EE := ((HW.log _ (getElem!_mem (by rw [HWf.len_log]; exact hn'))).2 en hem).2
  try wp_auto
  wp_apply wp_At lg _ uk en $$ [Hlg] as %ge #Hge
  · iframe Hlg; ipureintro; rw [Huk]; exact he
  try wp_auto
  wp_apply wp_IsConf ge en $$ [Hge]
  · iexact Hge
  cases hic : isConf en <;> rw [hic] at Ho
  · simp only [Bool.not_false, ite_true, pure_ok, Except.ok.injEq] at Ho
    subst Ho
    try wp_auto
    iapply HΦ; iunfold succOwn; ipureintro; rfl
  simp only [Bool.not_true, Bool.false_eq_true, ite_false] at Ho
  obtain ⟨r, hr, Ho⟩ := bind_ok Ho
  try wp_auto
  wp_apply wp_load_at _ _ ca Hn $$ [Hcaa]
  · iexact Hcaa
  try wp_auto
  have hca1 : sint.Z (ca + W64 1) = s.confAt[sint.nat n]! + 1 := by
    rw [sint_add (by rw [Hca, sint_one]; omega) (by rw [Hca, sint_one]; omega), Hca, sint_one]
  have hk1 : sint.Z (uk - W64 1) = k - 1 := by
    rw [sint_sub (by rw [Huk, sint_one]; omega) (by rw [Huk, sint_one]; omega), Huk, sint_one]
  ihave IH : iprop(∃ (qv : w64),
      "q" ∷ q_ptr ↦ qv ∗
      "%Hq" ∷ ⌜s.confAt[sint.nat n]! + 1 ≤ sint.Z qv ∧ sint.Z qv ≤ k ∧
        anyM ((List.range (k - (s.confAt[sint.nat n]! + 1)).toNat).drop (sint.Z qv - (s.confAt[sint.nat n]! + 1)).toNat)
          (fun i => do let e ← atE s.log[sint.nat n]! (s.confAt[sint.nat n]! + 1 + ↑i); Pure.pure (isConf e)) = .ok r⌝)
      $$ [q]
  · iexists _
    iframe
    ipureintro
    rw [hca1]
    refine ⟨Int.le_refl _, by omega, by simpa using hr⟩
  wp_for IH
  obtain ⟨hq0, hq1, hqS⟩ := Hq
  try wp_auto
  rw [hk1]
  wp_if_destruct
  · -- `q <= k - 1`: entry `q`
    have hj : (sint.Z qv - (s.confAt[sint.nat n]! + 1)).toNat < (k - (s.confAt[sint.nat n]! + 1)).toNat := by omega
    rw [List.drop_eq_getElem_cons (by simpa using hj), anyM_cons] at hqS
    simp only [List.getElem_range] at hqS
    obtain ⟨cq, hcq, hqS⟩ := bind_ok hqS
    obtain ⟨eq, heq, hcq⟩ := bind_ok hcq
    simp only [pure_ok, Except.ok.injEq] at hcq
    subst hcq
    have hqi : s.confAt[sint.nat n]! + 1 + ↑(sint.Z qv - (s.confAt[sint.nat n]! + 1)).toNat = sint.Z qv := by omega
    rw [hqi] at heq
    wp_apply wp_At lg _ qv eq $$ [Hlg] as %geq #Hgeq
    · iframe Hlg; ipureintro; exact heq
    try wp_auto
    wp_apply wp_IsConf geq eq $$ [Hgeq]
    · iexact Hgeq
    cases hiq : isConf eq <;> rw [hiq] at hqS
    · simp only [Bool.false_eq_true, ite_false] at hqS
      try wp_auto
      wp_for_post
      iframe
      iexists _
      iframe
      ipureintro
      have hq' : sint.Z (qv + W64 1) = sint.Z qv + 1 := sint_add_one (by omega)
      rw [hq']
      refine ⟨by omega, by omega, ?_⟩
      rw [show (sint.Z qv + 1 - (s.confAt[sint.nat n]! + 1)).toNat = (sint.Z qv - (s.confAt[sint.nat n]! + 1)).toNat + 1 by omega]
      exact hqS
    · simp only [ite_true, pure_ok, Except.ok.injEq] at hqS
      subst hqS
      simp only [ite_true, pure_ok, Except.ok.injEq] at Ho
      try wp_auto
      wp_for_post
      subst Ho
      try wp_auto
      iapply HΦ; iunfold succOwn; ipureintro; rfl
  have hqk : sint.Z qv = k := by omega
  rw [hqk, List.drop_eq_nil_of_le (by simp)] at hqS
  cases hqS
  simp only [Bool.false_eq_true, ite_false] at Ho
  try wp_auto
  -- `Legal(s.Config[n], At(logn, k).Value)`
  obtain ⟨e2, he2, Ho⟩ := bind_ok Ho
  rw [he] at he2; cases he2
  obtain ⟨lgv, hlgv, Ho⟩ := bind_ok Ho
  icases confsRO_at g.Config' s.config n ⟨Hn, by rw [HWf.len_config]; exact Hlt⟩ $$ HConfig with ⟨%gcv, #Hgcva, #Hgcv⟩
  have hcw := HW.config _ (getElem!_mem (by rw [HWf.len_config]; exact hn'))
  have hlb := legal_bounds (w := ev.size + 2) hcw heb hEE
  ihave #Hge' := Hge
  iunfold entryRO at Hge'
  icases Hge' with ⟨%Hge1, #Hgv⟩
  wp_apply wp_load_at _ _ gcv Hn $$ [Hgcva]
  · iexact Hgcva
  try wp_auto
  wp_apply wp_At lg _ uk en $$ [Hlg] as %ge2 #Hge2
  · iframe Hlg; ipureintro; rw [Huk]; exact he
  ihave #Hge2' := Hge2
  iunfold entryRO at Hge2'
  icases Hge2' with ⟨%-, #Hgv2⟩
  try wp_auto
  wp_apply wp_Legal gcv _ ge2.Value' en.value lgv $$ [Hgcv Hgv2]
  · iframe Hgcv Hgv2; ipureintro; exact ⟨hlgv, hlb⟩
  cases lgv
  · simp only [Bool.not_false, ite_true, pure_ok, Except.ok.injEq] at Ho
    subst Ho
    try wp_auto
    iapply HΦ; iunfold succOwn; ipureintro; rfl
  simp only [Bool.not_true, Bool.false_eq_true, ite_false] at Ho
  -- `s.Role[n] == Leader && !RecordedIn(s.Chain, s.TermLen, logn, k, s.CurrentTerm[n])`
  obtain ⟨rb, hrb, Ho⟩ := bind_ok Ho
  obtain ⟨xr, hxr, htr, hfr⟩ := andM_ok hrb
  simp only [pure_ok, Except.ok.injEq] at hxr
  subst hxr
  ihave #Hrla := strsRO_at g.Role' s.role n ⟨Hn, by rw [HWf.len_role]; exact Hlt⟩ $$ HRole
  icases intsRO_at g.CurrentTerm' s.currentTerm n ⟨Hn, by rw [HWf.len_currentTerm]; exact Hlt⟩ $$ HCurrentTerm with ⟨%ct, #Hcta, %Hct⟩
  try wp_auto
  wp_apply wp_load_at _ _ _ Hn $$ [Hrla] as -
  · iexact Hrla
  try wp_auto
  try rw [show (github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Leader : val) = #leader from rfl]
  by_cases hrl0 : s.role[sint.nat n]! = go!"leader"
  · have hrl : s.role[sint.nat n]! = leader := hrl0
    rw [decide_eq_true hrl0]
    have hnr := htr (beq_of_eq' hrl)
    unfold notM at hnr
    obtain ⟨rc, hrc, hnr⟩ := bind_ok hnr
    simp only [pure_ok, Except.ok.injEq] at hnr
    subst hnr
    try wp_auto
    wp_apply wp_load_at _ _ ct Hn $$ [Hcta]
    · iexact Hcta
    try wp_auto
    wp_apply wp_RecordedIn g.Chain' s.chain g.TermLen' s.termLen lg _ uk ct rc $$ [HChain HTermLen Hlg]
    · iframe HChain HTermLen Hlg; ipureintro; rw [Huk, Hct]; exact hrc
    cases rc
    · simp only [Bool.not_false, ite_true, pure_ok, Except.ok.injEq] at Ho
      subst Ho
      try wp_auto
      iapply HΦ; iunfold succOwn; ipureintro; rfl
    simp only [Bool.not_true, Bool.false_eq_true, ite_false] at Ho
    try wp_auto
    -- `c := NextConf(s.Config[n], At(logn, k).Value)`, `SameConf(ev, c)`
    obtain ⟨e3, he3, Ho⟩ := bind_ok Ho
    rw [he] at he3; cases he3
    obtain ⟨c, hc, Ho⟩ := bind_ok Ho
    obtain ⟨sm, hsm, Ho⟩ := bind_ok Ho
    wp_apply wp_load_at _ _ gcv Hn $$ [Hgcva]
    · iexact Hgcva
    try wp_auto
    wp_apply wp_At lg _ uk en $$ [Hlg] as %ge3 #Hge3
    · iframe Hlg; ipureintro; rw [Huk]; exact he
    ihave #Hge3' := Hge3
    iunfold entryRO at Hge3'
    icases Hge3' with ⟨%-, #Hgv3⟩
    try wp_auto
    wp_apply wp_NextConf gcv _ ge3.Value' en.value c $$ [Hgcv Hgv3] as %gc #Hgc
    · iframe Hgcv Hgv3; ipureintro; exact ⟨hc, hlb⟩
    try wp_auto
    wp_apply wp_SameConf e ev gc c sm $$ [He Hgc]
    · iframe He Hgc; ipureintro; exact ⟨hsm, by omega⟩
    cases sm
    · simp only [Bool.not_false, ite_true, pure_ok, Except.ok.injEq] at Ho
      subst Ho
      try wp_auto
      iapply HΦ; iunfold succOwn; ipureintro; rfl
    simp only [Bool.not_true, Bool.false_eq_true, ite_false] at Ho
    try wp_auto
    wp_apply wp_clone p s $$ [Hs] as %q Hq
    · iexact Hs
    try wp_auto
    wp_apply wp_setConf g.Config' s.config n gc c $$ [HConfig Hgc] as %co #Hco
    · iframe HConfig Hgc; ipureintro; exact ⟨Hn, by rw [HWf.len_config]; exact Hlt⟩
    try wp_auto
    wp_apply wp_set_config q s co (s.config.set (sint.nat n) c) (by rw [List.length_set, HWf.len_config]) $$ [Hq Hco] as Hq
    · iframe Hq Hco
    try wp_auto
    wp_apply wp_load_at _ _ _ Hn $$ [Hrla] as -
    · iexact Hrla
    try wp_auto
    try rw [show (github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Leader : val) = #leader from rfl]
    first | rw [decide_eq_true hrl] | rw [decide_eq_true hrl0]
    try wp_auto
    try rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.TermConfs.TypeAssumptions.ptr_With_unfold.method_unfold]
    try wp_auto
    wp_apply wp_load_at _ _ ct Hn $$ [Hcta]
    · iexact Hcta
    try wp_auto
    try rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.TermConfs.TypeAssumptions.ptr_With_unfold.method_unfold]
    try wp_auto
    wp_apply wp_ConfWith g.LedConf' s.ledConf ct gc c $$ [HLedConf Hgc] as %lc #Hlc
    · iframe HLedConf Hgc; ipureintro; have := HW.ledConf_len; omega
    try wp_auto
    wp_apply wp_set_ledConf q { s with config := s.config.set (sint.nat n) c } lc (s.ledConf.with (sint.Z ct) c) $$ [Hq Hlc] as Hq
    · iframe Hq Hlc
    try wp_auto
    try rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.TermInts.TypeAssumptions.ptr_With_unfold.method_unfold]
    try wp_auto
    wp_apply wp_load_at _ _ ct Hn $$ [Hcta]
    · iexact Hcta
    try wp_auto
    try rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.TermInts.TypeAssumptions.ptr_With_unfold.method_unfold]
    try wp_auto
    wp_apply wp_IntWith g.LedAt' s.ledAt ct uk $$ [HLedAt] as %lt #Hlt'
    · iframe HLedAt; ipureintro; have := HW.ledAt.1; omega
    try wp_auto
    wp_apply wp_set_ledAt q { { s with config := s.config.set (sint.nat n) c } with ledConf := s.ledConf.with (sint.Z ct) c } lt (s.ledAt.with (sint.Z ct) (sint.Z uk)) $$ [Hq Hlt'] as Hq
    · iframe Hq Hlt'
    try wp_auto
    wp_apply wp_setInt g.ConfAt' s.confAt n uk $$ [HConfAt] as %cao #Hcao
    · iframe HConfAt; ipureintro; exact ⟨Hn, by rw [HWf.len_confAt]; exact Hlt⟩
    try wp_auto
    wp_apply wp_set_confAt q { { { s with config := s.config.set (sint.nat n) c } with ledConf := s.ledConf.with (sint.Z ct) c } with ledAt := s.ledAt.with (sint.Z ct) (sint.Z uk) } cao (s.confAt.set (sint.nat n) (sint.Z uk)) (by simp [List.length_set, HWf.len_confAt]) $$ [Hq Hcao] as Hq
    · iframe Hq Hcao
    try wp_auto
    rw [Huk, Hct] at *
    have hO : o = some { { { { s with config := s.config.set (sint.nat n) c } with ledConf := s.ledConf.with s.currentTerm[sint.nat n]! c } with ledAt := s.ledAt.with s.currentTerm[sint.nat n]! k } with confAt := s.confAt.set (sint.nat n) k } := by
      simp only [beq_of_eq' hrl, ite_true, ite_false, Bool.false_eq_true, pure_ok, Except.ok.injEq] at Ho
      rw [← Ho]
    subst hO
    iapply HΦ
    iunfold succOwn
    isplitr
    · ipureintro; rfl
    iexact Hq
  · have hrl : ¬ s.role[sint.nat n]! = leader := hrl0
    rw [decide_eq_false hrl0]
    rw [hfr (beq_of_ne' hrl)] at Ho
    simp only [Bool.false_eq_true, ite_false] at Ho
    try wp_auto
    -- `c := NextConf(s.Config[n], At(logn, k).Value)`, `SameConf(ev, c)`
    obtain ⟨e3, he3, Ho⟩ := bind_ok Ho
    rw [he] at he3; cases he3
    obtain ⟨c, hc, Ho⟩ := bind_ok Ho
    obtain ⟨sm, hsm, Ho⟩ := bind_ok Ho
    wp_apply wp_load_at _ _ gcv Hn $$ [Hgcva]
    · iexact Hgcva
    try wp_auto
    wp_apply wp_At lg _ uk en $$ [Hlg] as %ge3 #Hge3
    · iframe Hlg; ipureintro; rw [Huk]; exact he
    ihave #Hge3' := Hge3
    iunfold entryRO at Hge3'
    icases Hge3' with ⟨%-, #Hgv3⟩
    try wp_auto
    wp_apply wp_NextConf gcv _ ge3.Value' en.value c $$ [Hgcv Hgv3] as %gc #Hgc
    · iframe Hgcv Hgv3; ipureintro; exact ⟨hc, hlb⟩
    try wp_auto
    wp_apply wp_SameConf e ev gc c sm $$ [He Hgc]
    · iframe He Hgc; ipureintro; exact ⟨hsm, by omega⟩
    cases sm
    · simp only [Bool.not_false, ite_true, pure_ok, Except.ok.injEq] at Ho
      subst Ho
      try wp_auto
      iapply HΦ; iunfold succOwn; ipureintro; rfl
    simp only [Bool.not_true, Bool.false_eq_true, ite_false] at Ho
    try wp_auto
    wp_apply wp_clone p s $$ [Hs] as %q Hq
    · iexact Hs
    try wp_auto
    wp_apply wp_setConf g.Config' s.config n gc c $$ [HConfig Hgc] as %co #Hco
    · iframe HConfig Hgc; ipureintro; exact ⟨Hn, by rw [HWf.len_config]; exact Hlt⟩
    try wp_auto
    wp_apply wp_set_config q s co (s.config.set (sint.nat n) c) (by rw [List.length_set, HWf.len_config]) $$ [Hq Hco] as Hq
    · iframe Hq Hco
    try wp_auto
    wp_apply wp_load_at _ _ _ Hn $$ [Hrla] as -
    · iexact Hrla
    try wp_auto
    try rw [show (github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Leader : val) = #leader from rfl]
    first | rw [decide_eq_false hrl] | rw [decide_eq_false hrl0]
    try wp_auto
    wp_apply wp_setInt g.ConfAt' s.confAt n uk $$ [HConfAt] as %cao #Hcao
    · iframe HConfAt; ipureintro; exact ⟨Hn, by rw [HWf.len_confAt]; exact Hlt⟩
    try wp_auto
    wp_apply wp_set_confAt q { s with config := s.config.set (sint.nat n) c } cao (s.confAt.set (sint.nat n) (sint.Z uk)) (by simp [List.length_set, HWf.len_confAt]) $$ [Hq Hcao] as Hq
    · iframe Hq Hcao
    try wp_auto
    rw [Huk] at *
    have hO : o = some { { s with config := s.config.set (sint.nat n) c } with confAt := s.confAt.set (sint.nat n) k } := by
      simp only [beq_of_ne' hrl, ite_true, ite_false, Bool.false_eq_true, pure_ok, Except.ok.injEq] at Ho
      rw [← Ho]
    subst hO
    iapply HΦ
    iunfold succOwn
    isplitr
    · ipureintro; rfl
    iexact Hq

end proof

end AntCheck
end EtcdGrove
end Perennial

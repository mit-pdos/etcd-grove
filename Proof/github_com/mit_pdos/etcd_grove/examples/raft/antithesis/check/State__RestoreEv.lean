/-
Lean-first (no Rocq counterpart). #33 S3b W2 (2026-11-23): the proof of `State.RestoreEv` (B 634-643).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State__RestoreEv
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State__clone
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Event__index
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Event__has
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.SubSeq
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.EntriesEqual
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.setInt
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.setPre
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State__InitConf
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.ConfOf
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.SameConf
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.StateLaws
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.EvalLaws
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.ActionLaws

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

theorem State.RestoreEv.wp_proof
    (wp_clone : State.clone.spec (GF := GF) (hG := hG))
    (wp_index : Event.index.spec (GF := GF) (hG := hG))
    (wp_has : Event.has.spec (GF := GF) (hG := hG))
    (wp_SubSeq : SubSeq.spec (GF := GF) (hG := hG))
    (wp_EntriesEqual : EntriesEqual.spec (GF := GF) (hG := hG))
    (wp_setInt : setInt.spec (GF := GF) (hG := hG))
    (wp_setPre : setPre.spec (GF := GF) (hG := hG))
    (wp_InitConf : State.InitConf.spec (GF := GF) (hG := hG))
    (wp_ConfOf : ConfOf.spec (GF := GF) (hG := hG))
    (wp_SameConf : SameConf.spec (GF := GF) (hG := hG)) :
    State.RestoreEv.spec (GF := GF) (hG := hG) := by
  intro p s n e ev o
  wp_start as ⟨#Hs, #He, %Hn, %Hlt, %HBd, %Ho⟩
  ihave #Hs' := Hs
  iunfold stateRO at Hs'
  iNamed Hs'
  iNamed Hf
  iStructNamed Hp

  obtain ⟨bb, EE, HW, HNO, -, hbb, hEE⟩ := HBd
  unfold numBound Event.weight at hbb
  unfold State.restoreEv at Ho
  obtain ⟨k, hk, Ho⟩ := bind_ok Ho
  have hkn : numOk k := by have := HNO.2.2.2.2.2.2.2.2.1; rw [need_ok hk] at this; exact this
  unfold numOk numBound at hkn
  icases logsRO_at g.Log' s.log n ⟨Hn, by rw [HWf.len_log]; exact Hlt⟩ $$ HLog with ⟨%lg, #Hlga, #Hlg⟩
  ihave %Hlgl := logRO_len _ _ $$ Hlg
  ihave %Hchl := logRO_len _ _ $$ HChain
  wp_auto
  wp_apply wp_index e ev k $$ [He] as %uk %Huk
  · iframe He; ipureintro; exact hk
  try wp_auto
  wp_apply wp_load_at _ _ lg Hn $$ [Hlga]
  · iexact Hlga
  try wp_auto
  rw [Huk, Hlgl]
  by_cases h2 : k ≤ (s.log[sint.nat n]!).length ∧ k ≤ s.chain.length
  case neg =>
    have : (!(decide (k ≤ ↑s.log[sint.nat n]!.length) && decide (k ≤ ↑s.chain.length))) = true := by
      simp only [Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not]; omega
    rw [this] at Ho
    simp only [ite_true, pure_ok, Except.ok.injEq] at Ho
    by_cases h2a : k ≤ (s.log[sint.nat n]!).length
    · rw [decide_eq_true h2a]
      try wp_auto
      rw [Huk, Hchl, decide_eq_false (by omega)]
      subst Ho
      try wp_auto
      iapply HΦ; iunfold succOwn; ipureintro; rfl
    · rw [decide_eq_false h2a]
      subst Ho
      try wp_auto
      iapply HΦ; iunfold succOwn; ipureintro; rfl
  rw [decide_eq_true h2.1]
  try wp_auto
  rw [Huk, Hchl, decide_eq_true h2.2]
  have : (!(decide (k ≤ ↑s.log[sint.nat n]!.length) && decide (k ≤ ↑s.chain.length))) = false := by
    simp only [Bool.not_eq_false', Bool.and_eq_true, decide_eq_true_eq]; omega
  rw [this] at Ho
  simp only [Bool.false_eq_true, ite_false] at Ho
  obtain ⟨sc, hsc, Ho⟩ := bind_ok Ho
  obtain ⟨sl, hsl, Ho⟩ := bind_ok Ho
  obtain ⟨eq1, heq1, Ho⟩ := bind_ok Ho
  try wp_auto
  wp_apply wp_SubSeq g.Chain' s.chain (W64 1) uk sc $$ [HChain] as %scl #Hsc
  · iframe HChain; ipureintro; rw [Huk, sint_one]; exact hsc
  try wp_auto
  wp_apply wp_load_at _ _ lg Hn $$ [Hlga]
  · iexact Hlga
  try wp_auto
  wp_apply wp_SubSeq lg _ (W64 1) uk sl $$ [Hlg] as %sll #Hsl
  · iframe Hlg; ipureintro; rw [Huk, sint_one]; exact hsl
  try wp_auto
  wp_apply wp_EntriesEqual scl sc sll sl eq1 $$ [Hsc Hsl]
  · iframe Hsc Hsl; ipureintro; exact heq1
  cases eq1
  · simp only [Bool.not_false, ite_true, pure_ok, Except.ok.injEq] at Ho
    subst Ho
    try wp_auto
    iapply HΦ; iunfold succOwn; ipureintro; rfl
  simp only [Bool.not_true, Bool.false_eq_true, ite_false] at Ho
  try wp_auto
  wp_apply wp_clone p s $$ [Hs] as %q Hq
  · iexact Hs
  try wp_auto
  wp_apply wp_setInt g.LastApplied' s.lastApplied n uk $$ [HLastApplied] as %lao #Hlao
  · iframe HLastApplied; ipureintro; exact ⟨Hn, by rw [HWf.len_lastApplied]; exact Hlt⟩
  try wp_auto
  wp_apply wp_set_lastApplied q s lao (s.lastApplied.set (sint.nat n) (sint.Z uk)) (by rw [List.length_set, HWf.len_lastApplied]) $$ [Hq Hlao] as Hq
  · iframe Hq Hlao
  try wp_auto
  rw [Huk]
  -- `SameConf(ev, ConfOf(s.Chain, k, s.InitConf()))`
  obtain ⟨cc, hcc, Ho⟩ := bind_ok Ho
  obtain ⟨sm, hsm, Ho⟩ := bind_ok Ho
  wp_apply wp_InitConf p s $$ [Hs] as %ic #Hic
  · iexact Hs
  try wp_auto
  wp_apply wp_ConfOf g.Chain' s.chain uk ic s.initConf cc $$ [HChain Hic] as %gcc #Hcc
  · iframe HChain Hic; ipureintro; refine ⟨by rw [Huk]; exact hcc, by omega, confOf_bounded_init HW hEE⟩
  try wp_auto
  wp_apply wp_SameConf e ev gcc cc sm $$ [He Hcc]
  · iframe He Hcc; ipureintro; exact ⟨hsm, by omega⟩
  cases sm
  · simp only [Bool.not_false, ite_true, pure_ok, Except.ok.injEq] at Ho
    subst Ho
    try wp_auto
    iapply HΦ; iunfold succOwn; ipureintro; rfl
  simp only [Bool.not_true, Bool.false_eq_true, ite_false] at Ho
  try wp_auto
  rw [show (github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.FA : val) = #fA from rfl]
  wp_apply wp_has e ev fA ev.a $$ [He]
  · iframe He; ipureintro; exact Event.hasF_A _
  cases ha : ev.a
  · simp only [Bool.not_false, ite_true]
    try wp_auto
    wp_apply wp_setPre g.Undo' s.undo n null none $$ [HUndo] as %uo #Huo
    · iframe HUndo; iunfold preRO; ipureintro; exact ⟨rfl, Hn, by rw [HWf.len_undo]; exact Hlt⟩
    try wp_auto
    wp_apply wp_set_undo q { s with lastApplied := s.lastApplied.set (sint.nat n) k } uo (s.undo.set (sint.nat n) none) (by rw [List.length_set, HWf.len_undo]) $$ [Hq Huo] as Hq
    · iframe Hq Huo
    try wp_auto
    have hO : o = some { { s with lastApplied := s.lastApplied.set (sint.nat n) k } with undo := s.undo.set (sint.nat n) none } := by
      simp [ha] at Ho; rw [← Ho]
    subst hO
    iapply HΦ
    iunfold succOwn
    isplitr
    · ipureintro; rfl
    iexact Hq
  · simp only [Bool.not_true, Bool.false_eq_true, ite_false]
    try wp_auto
    have hO : o = some { s with lastApplied := s.lastApplied.set (sint.nat n) k } := by
      simp [ha] at Ho; rw [← Ho]
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

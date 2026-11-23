/-
Lean-first (no Rocq counterpart). #33 S3b W6 (2026-11-23): the proof of `State.Ready` (B 439-447).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State__Ready
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State__InMemory
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State__OnDisk
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State__queued
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.StateLaws
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.EvalLaws
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

theorem State.Ready.wp_proof (onDisk_keeps : W6Laws.OnDiskKeeps) (inMemory_lengths : W6Laws.InMemoryLengths)
    (inMemory_within : InMemoryWithin)
    (wp_InMemory : State.InMemory.spec (GF := GF) (hG := hG))
    (wp_OnDisk : State.OnDisk.spec (GF := GF) (hG := hG))
    (wp_queued : State.queued.spec (GF := GF) (hG := hG)) :
    State.Ready.spec (GF := GF) (hG := hG) := by
  intro p s n e ev o
  wp_start as ⟨#Hs, #He, %Hn, %Hlt, %HBd, %Ho⟩
  ihave #Hs' := Hs
  iunfold stateRO at Hs'
  iNamed Hs'
  iNamed Hf
  iStructNamed Hp
  have HBd' := HBd
  obtain ⟨bb, EE, HW, HNO, HCh, hbb, -⟩ := HBd'
  have hw2 : ev.weight = ev.size + 2 := rfl
  unfold State.ready at Ho
  icases queueRO_at g.Queue' s.queue n ⟨Hn, by rw [HWf.len_queue]; exact Hlt⟩ $$ HQueue with ⟨%qv, #Hqa, #Hq⟩
  ihave %Hql := qitemsRO_len _ _ $$ Hq
  wp_auto
  wp_apply wp_load_at _ _ qv Hn $$ [Hqa]
  · iexact Hqa
  try wp_auto
  by_cases hq0 : s.queue[sint.nat n]! = []
  case neg =>
    rw [ite_eq_left_of_eq_true _ _ (by simpa using hq0)] at Ho
    simp only [pure_ok, Except.ok.injEq] at Ho
    subst Ho
    have hne : qv.len ≠ W64 0 := by
      intro h; rw [h, sint_zero] at Hql; exact hq0 (List.eq_nil_of_length_eq_zero (by omega))
    rw [decide_eq_false hne]
    try wp_auto
    iapply HΦ; iunfold succOwn; ipureintro; rfl
  simp only [show (s.queue[sint.nat n]! != []) = false by simpa using hq0, Bool.false_eq_true, ite_false] at Ho
  have h0 : qv.len = W64 0 := by rw [hq0] at Hql; simp at Hql; word
  rw [h0]
  try wp_auto
  obtain ⟨r, hr, Ho⟩ := bind_ok Ho
  obtain ⟨hrl, hcl, hal⟩ := inMemory_lengths _ _ _ _ hr
  have hrW := inMemory_within s (sint.nat n) ev bb EE r (by have := sint_nat_cast Hn; omega) HW HNO HCh hbb hr
  wp_apply wp_InMemory p s n e ev r $$ [Hs He] as %gr Hr
  · iframe Hs He; ipureintro; exact ⟨Hn, Hlt, HBd, hr⟩
  iunfold memResultRO at Hr
  icases Hr with ⟨%Hok, #HrRole, #HrLeaders, #HrLedLog, #HrLedConf, #HrConfig, #HrConfAt, #HrLedAt, #HrElAt, #HrChain, #HrTermLen, #HrViol⟩
  try wp_auto
  rw [Hok]
  cases hro : r.ok
  · rw [hro] at Ho
    simp only [Bool.not_false, ite_true, pure_ok, Except.ok.injEq] at Ho
    subst Ho
    try wp_auto
    iapply HΦ; iunfold succOwn; ipureintro; rfl
  rw [hro] at Ho
  simp only [Bool.not_true, Bool.false_eq_true, ite_false] at Ho
  obtain ⟨qi, hqi, Ho⟩ := bind_ok Ho
  obtain ⟨o', hod, Ho⟩ := bind_ok Ho
  try wp_auto
  wp_apply wp_queued p s n e ev qi $$ [Hs He] as %gqi #Hgqi
  · iframe Hs He; ipureintro; exact ⟨Hn, Hlt, hqi⟩
  try wp_auto
  have HW1 := State.Within.mono' (b' := bb + ev.size + 1) (E' := EE) (by omega) (Nat.le_refl _) HW
  have hbd : OnDisk.Bounded (OnDisk.mk s (sint.nat n) qi false r.role r.leaders r.ledLog r.chain r.termLen r.viol) :=
    ⟨bb + ev.size + 1, EE, by rw [show bb + ev.size + 1 + 1 = bb + ev.weight by omega]; exact hbb,
      W6Laws.onDisk_within_ready HW1 hrW HW1.viol (W6Laws.queued_within HW1 ⟨HNO, by omega, HCh⟩ hqi)⟩
  wp_apply wp_OnDisk p s n gqi qi false gr.Role' r.role gr.Leaders' r.leaders gr.LedLog' r.ledLog gr.Chain' r.chain
    gr.TermLen' r.termLen gr.Viol' r.viol o' $$ [Hs Hgqi HrRole HrLeaders HrLedLog HrChain HrTermLen HrViol] as %q' %ok Hsucc
  · iframe Hs Hgqi HrRole HrLeaders HrLedLog HrChain HrTermLen HrViol
    ipureintro; exact ⟨Hn, Hlt, by rw [hrl, HWf.len_role], hbd, hod⟩
  try wp_auto
  cases o' with
  | none =>
    simp only [pure_ok, Except.ok.injEq] at Ho
    subst Ho
    iunfold succOwn at Hsucc
    icases Hsucc with %Hok'
    subst Hok'
    try wp_auto
    iapply HΦ; iunfold succOwn; ipureintro; rfl
  | some ns =>
  simp only [pure_ok, Except.ok.injEq] at Ho
  subst Ho
  iunfold succOwn at Hsucc
  icases Hsucc with ⟨%Hok', Hns⟩
  subst Hok'
  obtain ⟨hcfg, -, -, -⟩ := onDisk_keeps _ _ _ _ _ _ _ _ _ _ _ hod
  try wp_auto
  wp_apply wp_set_ledConf q' ns _ _ $$ [Hns HrLedConf] as Hns
  · iframe Hns HrLedConf
  try wp_auto
  wp_apply wp_set_ledAt q' ({ ns with ledConf := r.ledConf } : State) _ _ $$ [Hns HrLedAt] as Hns
  · iframe Hns HrLedAt
  try wp_auto
  wp_apply wp_set_elAt q' ({ ns with ledConf := r.ledConf, ledAt := r.ledAt } : State) _ _ $$ [Hns HrElAt] as Hns
  · iframe Hns HrElAt
  try wp_auto
  wp_apply wp_set_config q' ({ ns with ledConf := r.ledConf, ledAt := r.ledAt, elAt := r.elAt } : State) _ _
    (by rw [hcl, HWf.len_config, ← hcfg]) $$ [Hns HrConfig] as Hns
  · iframe Hns HrConfig
  try wp_auto
  wp_apply wp_set_confAt q' ({ ns with ledConf := r.ledConf, ledAt := r.ledAt, elAt := r.elAt, config := r.config } : State) _ _
    (by rw [hal, HWf.len_confAt, ← hcfg]) $$ [Hns HrConfAt] as Hns
  · iframe Hns HrConfAt
  try wp_auto
  iapply HΦ
  iunfold succOwn
  isplitr
  · ipureintro; rfl
  iexact Hns

end proof

end AntCheck
end EtcdGrove
end Perennial

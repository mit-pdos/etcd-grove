/-
Lean-first (no Rocq counterpart). #33 S3b W3a (2026-11-23): the proof of `x.ok()` (B 214-253, `InMem.ok`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.inMem__ok
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.inMem__T
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.inMem__leads
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.inMem__wins
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.inMem__snapsM
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.inMem__ll1
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.inMem__lc1
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.inMem__L
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.inMem__c
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.inMem__es
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.inMem__app
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.inMem__cmt
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Event__by
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Event__role
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Event__snap
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Event__has
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Event__first
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.validBy
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.TermLogs__Has
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.TermLogs__Get
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.TermConfs__Get
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State__Granted
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State__Acked
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State__OneWaiting
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State__AllSwitched
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.IsQuorum
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.RecordedIn
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.IsConf
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Legal
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.StateLaws
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.EvalLaws
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Init0Laws
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.InMemOkLaws
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.ActionLaws
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Within.Parts
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Within.Laws

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
/-- A check of `ok` fails: the Go stores `false` and returns (the join's second case). -/
local macro "okRet" : tactic =>
  `(tactic| ((try wp_auto); iright; iframe; ipureintro; exact ⟨by first | rfl | trivial, Hv.symm⟩))

set_option hygiene false in
/-- A block of `ok` passes: the Go falls through (the join's first case). -/
local macro "okNext" : tactic =>
  `(tactic| ((try wp_auto); ileft; iframe; ipureintro; exact ⟨by first | rfl | trivial, Hv⟩))

theorem inMem.ok.wp_proof
    (wp_T : inMem.T.spec (GF := GF) (hG := hG))
    (wp_leads : inMem.leads.spec (GF := GF) (hG := hG))
    (wp_wins : inMem.wins.spec (GF := GF) (hG := hG))
    (wp_snapsM : inMem.snapsM.spec (GF := GF) (hG := hG))
    (wp_ll1 : inMem.ll1.spec (GF := GF) (hG := hG))
    (wp_lc1 : inMem.lc1.spec (GF := GF) (hG := hG))
    (wp_L : inMem.L.spec (GF := GF) (hG := hG))
    (wp_c : inMem.c.spec (GF := GF) (hG := hG))
    (wp_es : inMem.es.spec (GF := GF) (hG := hG))
    (wp_app : inMem.app.spec (GF := GF) (hG := hG))
    (wp_cmt : inMem.cmt.spec (GF := GF) (hG := hG))
    (wp_by : Event.by.spec (GF := GF) (hG := hG))
    (wp_role : Event.role.spec (GF := GF) (hG := hG))
    (wp_snap : Event.snap.spec (GF := GF) (hG := hG))
    (wp_has : Event.has.spec (GF := GF) (hG := hG))
    (wp_first : Event.first.spec (GF := GF) (hG := hG))
    (wp_validBy : validBy.spec (GF := GF) (hG := hG))
    (wp_Has : TermLogs.Has.spec (GF := GF) (hG := hG))
    (wp_Get : TermLogs.Get.spec (GF := GF) (hG := hG))
    (wp_ConfGet : TermConfs.Get.spec (GF := GF) (hG := hG))
    (wp_Granted : State.Granted.spec (GF := GF) (hG := hG))
    (wp_Acked : State.Acked.spec (GF := GF) (hG := hG))
    (wp_OneWaiting : State.OneWaiting.spec (GF := GF) (hG := hG))
    (wp_AllSwitched : State.AllSwitched.spec (GF := GF) (hG := hG))
    (wp_IsQuorum : IsQuorum.spec (GF := GF) (hG := hG))
    (wp_RecordedIn : RecordedIn.spec (GF := GF) (hG := hG))
    (wp_IsConf : IsConf.spec (GF := GF) (hG := hG))
    (wp_Legal : Legal.spec (GF := GF) (hG := hG)) :
    inMem.ok.spec (GF := GF) (hG := hG) := by
  intro gx x v
  wp_start as ⟨#Hx, %Hv⟩
  ihave #Hx' := Hx
  iunfold inMemRO at Hx'
  icases Hx' with ⟨#Hs, #He, %Hp⟩
  obtain ⟨Hgn, Hnl, bb, EE, HW, HN, HC, hbb, hEE⟩ := Hp
  unfold numBound Event.weight at hbb
  ihave #Hs' := Hs
  iunfold stateRO at Hs'
  iNamed Hs'
  iNamed Hf
  iStructNamed Hp
  have hn0 : 0 ≤ sint.Z gx.n' := by rw [Hgn]; omega
  have hnl : sint.Z gx.n' < x.s.cfg.server.length := by rw [Hgn]; exact_mod_cast Hnl
  have hnn : sint.nat gx.n' = x.n := by have := sint_nat_cast hn0; omega
  ihave #Hroa := strsRO_at g.Role' x.s.role gx.n' ⟨hn0, by rw [HWf.len_role]; exact hnl⟩ $$ HRole
  icases intsRO_at g.CurrentTerm' x.s.currentTerm gx.n' ⟨hn0, by rw [HWf.len_currentTerm]; exact hnl⟩ $$ HCurrentTerm with ⟨%ctw, #Hcta, %Hct⟩
  icases intsRO_at g.ConfAt' x.s.confAt gx.n' ⟨hn0, by rw [HWf.len_confAt]; exact hnl⟩ $$ HConfAt with ⟨%caw, #Hcaa, %Hca⟩
  icases logsRO_at g.Log' x.s.log gx.n' ⟨hn0, by rw [HWf.len_log]; exact hnl⟩ $$ HLog with ⟨%lgs, #Hlga, #Hlg⟩
  icases confsRO_at g.Config' x.s.config gx.n' ⟨hn0, by rw [HWf.len_config]; exact hnl⟩ $$ HConfig with ⟨%cfv, #Hcfa, #Hcf⟩
  rw [hnn] at Hct Hca
  rw [hnn]
  rw [InMem.ok_eq] at Hv
  obtain ⟨bv, hbv, Hv⟩ := bind_ok Hv
  wp_auto
  wp_apply wp_by gx.ev' x.ev bv $$ [He]
  · iframe He; ipureintro; exact hbv
  try wp_auto
  wp_apply wp_validBy bv
  rw [InMem.validBy_contains]
  cases hvb : InMem.validByOk bv
  · simp only [hvb, Bool.not_false, ite_true, pure_ok, Except.ok.injEq] at Hv
    subst Hv
    try wp_auto
    iapply HΦ; ipureintro; trivial
  simp only [hvb, Bool.not_true, Bool.false_eq_true, ite_false] at Hv
  try wp_auto
  obtain ⟨r, hr, Hv⟩ := bind_ok Hv
  wp_apply wp_role gx.ev' x.ev r $$ [He]
  · iframe He; ipureintro; exact hr
  try wp_auto
  wp_join (v := #(InMem.okRoleOk r)) at (if: (if: _ then #true else _) then #true else _) with [r]
  · repeat' (first | wp_if_destruct | wp_auto)
    all_goals (iframe; ipureintro; first | (congr 1; done) | (congr 1; simp_all [InMem.okRoleOk, follower, candidate, leader]))
  cases hro : InMem.okRoleOk r
  · simp only [hro, Bool.not_false, ite_true, pure_ok, Except.ok.injEq] at Hv
    subst Hv
    try wp_auto
    iapply HΦ; ipureintro; trivial
  simp only [hro, Bool.not_true, Bool.false_eq_true, ite_false] at Hv
  try wp_auto
  unfold InMem.okSnap at Hv
  wp_join (Q := fun w => iprop((⌜w = executeVal ∧ x.okWins = .ok v⌝ ∗ x_ptr ↦ gx ∗ s_ptr ↦ gx.s' ∗ n_ptr ↦ gx.n' ∗
      ev_ptr ↦ gx.ev' ∗ «$res0_ptr» ↦ zero_val Bool) ∨ (⌜w = returnVal #() ∧ v = false⌝ ∗ «$res0_ptr» ↦ false)))
    at next with [x s n ev «$res0»]
  · rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.inMem.TypeAssumptions.ptr_snapsM_unfold.method_unfold]; try wp_auto
    wp_apply wp_snapsM gx x $$ [Hx]
    · iexact Hx
    cases hsm : x.snapsM with
    | false =>
      simp only [hsm, Bool.false_eq_true, ite_false] at Hv
      try wp_auto
      ileft; iframe; ipureintro; exact ⟨rfl, Hv⟩
    | true =>
      simp only [hsm, ite_true] at Hv
      try wp_auto
      obtain ⟨c, hc, Hv⟩ := bind_ok Hv
      obtain ⟨a1, ha1, ha1t, ha1f⟩ := andM_ok hc
      rw [hr, ok_bind, pure_ok, Except.ok.injEq] at ha1
      wp_apply wp_role gx.ev' x.ev r $$ [He]
      · iframe He; ipureintro; exact hr
      try wp_auto
      by_cases hrl : r = leader
      · rw [decide_eq_true (show r = go!"leader" from hrl)]
        have : a1 = false := by rw [← ha1, hrl]; rfl
        rw [ha1f this] at Hv
        simp only [Bool.not_false, ite_true, pure_ok, Except.ok.injEq] at Hv
        try wp_auto
        iright; iframe; ipureintro; exact ⟨rfl, Hv.symm⟩
      rw [decide_eq_false (show ¬ r = go!"leader" from hrl)]
      have : a1 = true := by rw [← ha1]; simpa using hrl
      have hc2 := ha1t this
      obtain ⟨a2, ha2, ha2t, ha2f⟩ := andM_ok hc2
      simp only [pure_ok, Except.ok.injEq] at ha2
      try wp_auto
      wp_apply wp_load_at _ _ _ hn0 $$ [Hroa]
      · iexact Hroa
      try iintro -
      try wp_auto
      by_cases hsl : x.s.role[x.n]! = leader
      · rw [decide_eq_true (show x.s.role[x.n]! = go!"leader" from hsl)]
        have : (x.s.role[x.n]! != leader) = false := by simp [hsl]
        rw [ha2f (ha2.symm.trans this)] at Hv
        simp only [Bool.not_false, ite_true, pure_ok, Except.ok.injEq] at Hv
        try wp_auto
        iright; iframe; ipureintro; exact ⟨rfl, Hv.symm⟩
      rw [decide_eq_false (show ¬ x.s.role[x.n]! = go!"leader" from hsl)]
      have hc3 := ha2t (by rw [← ha2]; simpa using hsl)
      obtain ⟨sn, hsn, hc3⟩ := bind_ok hc3
      simp only [pure_ok, Except.ok.injEq] at hc3
      subst hc3
      try wp_auto
      wp_apply wp_snap gx.ev' x.ev sn $$ [He] as %us %Hus
      · iframe He; ipureintro; exact hsn
      ihave %Hchl := logRO_len _ _ $$ HChain
      try wp_auto
      rw [Hus.1, Hchl]
      by_cases hsi : sn.index ≤ x.s.chain.length
      · rw [decide_eq_true hsi]
        simp only [hsi, decide_true, Bool.not_true, Bool.false_eq_true, ite_false] at Hv
        try wp_auto
        ileft; iframe; ipureintro; exact ⟨rfl, Hv⟩
      · rw [decide_eq_false hsi]
        simp only [hsi, decide_false, Bool.not_false, ite_true, pure_ok, Except.ok.injEq] at Hv
        try wp_auto
        iright; iframe; ipureintro; exact ⟨rfl, Hv.symm⟩
  rename_i w
  iintro Hw
  icases Hw with (⟨%Hw, x, s, n, ev, «$res0»⟩ | ⟨%Hw, «$res0»⟩)
  rotate_left
  · obtain ⟨rfl, rfl⟩ := Hw
    try wp_auto
    iapply HΦ; ipureintro; trivial
  obtain ⟨rfl, Hv⟩ := Hw
  try wp_auto
  unfold InMem.okWins at Hv
  obtain ⟨wn, hwn, Hv⟩ := bind_ok Hv
  wp_join (Q := fun w => iprop((⌜w = executeVal ∧ x.okLeads = .ok v⌝ ∗ x_ptr ↦ gx ∗ s_ptr ↦ gx.s' ∗ n_ptr ↦ gx.n' ∗
      ev_ptr ↦ gx.ev' ∗ «$res0_ptr» ↦ zero_val Bool) ∨ (⌜w = returnVal #() ∧ v = false⌝ ∗ «$res0_ptr» ↦ false)))
    at next with [x s n ev «$res0»]
  · rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.inMem.TypeAssumptions.ptr_wins_unfold.method_unfold]; try wp_auto
    wp_apply wp_wins gx x wn $$ [Hx]
    · iframe Hx; ipureintro; exact hwn
    cases wn with
    | false =>
      simp only [Bool.false_eq_true, ite_false] at Hv
      okNext
    | true =>
      simp only [ite_true] at Hv
      try wp_auto
      obtain ⟨c1, hc1, Hv⟩ := bind_ok Hv
      obtain ⟨a1, ha1, ha1t, ha1f⟩ := andM_ok hc1
      simp only [pure_ok, Except.ok.injEq] at ha1
      wp_apply wp_load_at _ _ _ hn0 $$ [Hroa]
      · iexact Hroa
      try iintro -
      try wp_auto
      by_cases hrc : x.s.role[x.n]! = candidate
      case neg =>
        rw [decide_eq_false (show ¬ x.s.role[x.n]! = go!"candidate" from hrc)]
        rw [ha1f (by rw [← ha1]; simpa using hrc)] at Hv
        simp only [Bool.not_false, ite_true, pure_ok, Except.ok.injEq] at Hv
        okRet
      rw [decide_eq_true (show x.s.role[x.n]! = go!"candidate" from hrc)]
      have hc1' := ha1t (by rw [← ha1]; simpa using hrc)
      obtain ⟨t, ht, hc1'⟩ := bind_ok hc1'
      simp only [pure_ok, Except.ok.injEq] at hc1'
      try wp_auto
      wp_apply wp_load_at _ _ _ hn0 $$ [Hcta]
      · iexact Hcta
      try iintro -
      try wp_auto
      rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.inMem.TypeAssumptions.ptr_T_unfold.method_unfold]; try wp_auto
      wp_apply wp_T gx x t $$ [Hx] as %ut %Hut
      · iframe Hx; ipureintro; exact ht
      try wp_auto
      rw [decide_w64_eq, Hct, Hut]
      by_cases hct : x.s.currentTerm[x.n]! = t
      case neg =>
        rw [decide_eq_false hct]
        rw [← hc1', show (x.s.currentTerm[x.n]! == t) = false by simpa using hct] at Hv
        simp only [Bool.not_false, ite_true, pure_ok, Except.ok.injEq] at Hv
        okRet
      rw [decide_eq_true hct]
      rw [← hc1', show (x.s.currentTerm[x.n]! == t) = true by simpa using hct] at Hv
      simp only [Bool.not_true, Bool.false_eq_true, ite_false, ht, ok_bind] at Hv
      try wp_auto
      rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.inMem.TypeAssumptions.ptr_T_unfold.method_unfold]; try wp_auto
      wp_apply wp_T gx x t $$ [Hx] as %ut2 %Hut2
      · iframe Hx; ipureintro; exact ht
      rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.TermLogs.TypeAssumptions.ptr_Has_unfold.method_unfold]
      try wp_auto
      wp_apply wp_Has g.LedLog' x.s.ledLog ut2 $$ [HLedLog]
      · iexact HLedLog
      rw [Hut2]
      cases hlh : x.s.ledLog.has t with
      | true =>
        simp only [hlh, ite_true, pure_ok, Except.ok.injEq] at Hv
        okRet
      | false =>
      simp only [hlh, Bool.false_eq_true, ite_false] at Hv
      try wp_auto
      have hsrv : (x.s.cfg.server.length : Int) < 2 ^ 61 := HW.cfg.1
      wp_apply wp_Granted gx.s' x.s gx.n' $$ [Hs] as %ugr #Hgr
      · iframe Hs; ipureintro; exact ⟨hn0, hnl, hsrv⟩
      rw [hnn]
      try wp_auto
      wp_apply wp_load_at _ _ _ hn0 $$ [Hcfa]
      · iexact Hcfa
      try iintro -
      try wp_auto
      have hgl := State.granted_length_le x.s Hnl
      have hcw := HW.config _ (getElem!_mem (show x.n < x.s.config.length by rw [HWf.len_config]; exact Hnl))
      have hcl := confWithin_lt (w := x.ev.weight) hcw hEE
      wp_apply wp_IsQuorum ugr _ cfv _ $$ [Hgr Hcf]
      · iframe Hgr Hcf; ipureintro; exact ⟨by omega, hcl.1, hcl.2⟩
      try iintro -
      cases hq : isQuorum (x.s.granted x.n) x.s.config[x.n]! with
      | false =>
        simp only [hq, Bool.not_false, ite_true, pure_ok, Except.ok.injEq] at Hv
        okRet
      | true =>
      simp only [hq, Bool.not_true, Bool.false_eq_true, ite_false] at Hv
      try wp_auto
      have hcab : bigOk x.s.confAt[x.n]! :=
        HW.confAt _ (getElem!_mem (show x.n < x.s.confAt.length by rw [HWf.len_confAt]; exact Hnl))
      have hlgw : logWithin bb EE x.s.log[x.n]! :=
        HW.log _ (getElem!_mem (show x.n < x.s.log.length by rw [HWf.len_log]; exact Hnl))
      unfold bigOk at hcab
      wp_apply wp_load_at _ _ _ hn0 $$ [Hlga]
      · iexact Hlga
      try iintro -
      try wp_auto
      obtain ⟨ow, how, Hv⟩ := bind_ok Hv
      wp_apply wp_OneWaiting gx.s' x.s gx.n' lgs _ ow $$ [Hs Hlg]
      · iframe Hs Hlg; ipureintro; rw [hnn]; exact ⟨hn0, hnl, how, by omega, by have := hlgw.1; omega⟩
      try iintro -
      cases ow with
      | false =>
        simp only [Bool.not_false, ite_true, pure_ok, Except.ok.injEq] at Hv
        okRet
      | true =>
      simp only [Bool.not_true, Bool.false_eq_true, ite_false] at Hv
      try wp_auto
      obtain ⟨oc, hoc, Hv⟩ := bind_ok Hv
      obtain ⟨a0, ha0, ha0t, ha0f⟩ := orM_ok hoc
      simp only [pure_ok, Except.ok.injEq] at ha0
      wp_apply wp_load_at _ _ _ hn0 $$ [Hcaa]
      · iexact Hcaa
      try iintro -
      try wp_auto
      rw [decide_w64_eq, Hca, sint_zero]
      by_cases hc0 : x.s.confAt[x.n]! = 0
      · rw [decide_eq_true hc0]
        rw [ha0t (by rw [← ha0]; simpa using hc0)] at Hv
        simp only [Bool.not_true, Bool.false_eq_true, ite_false] at Hv
        okNext
      rw [decide_eq_false hc0]
      have hoc' := ha0f (by rw [← ha0]; simpa using hc0)
      have htb := InMem.T_bigOk HN ht
      unfold bigOk at htb
      try wp_auto
      wp_apply wp_load_at _ _ _ hn0 $$ [Hlga]
      · iexact Hlga
      try iintro -
      try wp_auto
      wp_apply wp_load_at _ _ _ hn0 $$ [Hcaa]
      · iexact Hcaa
      try iintro -
      try wp_auto
      rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.inMem.TypeAssumptions.ptr_T_unfold.method_unfold]; try wp_auto
      wp_apply wp_T gx x t $$ [Hx] as %ut3 %Hut3
      · iframe Hx; ipureintro; exact ht
      try wp_auto
      wp_apply wp_RecordedIn g.Chain' x.s.chain g.TermLen' x.s.termLen lgs _ caw (ut3 - W64 1) oc $$ [HChain HTermLen Hlg]
      · iframe HChain HTermLen Hlg; ipureintro
        rw [Hca, sint_sub (by rw [Hut3, sint_one]; omega) (by rw [Hut3, sint_one]; omega), Hut3, sint_one]
        exact hoc'
      try iintro -
      cases oc with
      | false =>
        simp only [Bool.not_false, ite_true, pure_ok, Except.ok.injEq] at Hv
        okRet
      | true =>
      simp only [Bool.not_true, Bool.false_eq_true, ite_false] at Hv
      okNext
  rename_i w
  iintro Hw
  icases Hw with (⟨%Hw, x, s, n, ev, «$res0»⟩ | ⟨%Hw, «$res0»⟩)
  rotate_left
  · obtain ⟨rfl, rfl⟩ := Hw
    try wp_auto
    iapply HΦ; ipureintro; trivial
  obtain ⟨rfl, Hv⟩ := Hw
  try wp_auto
  unfold InMem.okLeads at Hv
  obtain ⟨ld, hld, Hv⟩ := bind_ok Hv
  wp_join (Q := fun w => iprop((⌜w = executeVal ∧ x.okApp = .ok v⌝ ∗ x_ptr ↦ gx ∗ s_ptr ↦ gx.s' ∗ n_ptr ↦ gx.n' ∗
      ev_ptr ↦ gx.ev' ∗ «$res0_ptr» ↦ zero_val Bool) ∨ (⌜w = returnVal #() ∧ v = false⌝ ∗ «$res0_ptr» ↦ false)))
    at next with [x s n ev «$res0»]
  · rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.inMem.TypeAssumptions.ptr_leads_unfold.method_unfold]; try wp_auto
    wp_apply wp_leads gx x ld $$ [Hx]
    · iframe Hx; ipureintro; exact hld
    try iintro -
    cases ld with
    | false =>
      simp only [Bool.false_eq_true, ite_false] at Hv
      okNext
    | true =>
    simp only [ite_true] at Hv
    try wp_auto
    obtain ⟨c1, hc1, Hv⟩ := bind_ok Hv
    obtain ⟨a1, ha1, ha1t, ha1f⟩ := andM_ok hc1
    obtain ⟨t, ht, ha1⟩ := bind_ok ha1
    simp only [pure_ok, Except.ok.injEq] at ha1
    wp_apply wp_load_at _ _ _ hn0 $$ [Hcta]
    · iexact Hcta
    try iintro -
    try wp_auto
    rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.inMem.TypeAssumptions.ptr_T_unfold.method_unfold]; try wp_auto
    wp_apply wp_T gx x t $$ [Hx] as %ut %Hut
    · iframe Hx; ipureintro; exact ht
    try wp_auto
    rw [decide_w64_eq, Hct, Hut]
    by_cases hct : x.s.currentTerm[x.n]! = t
    case neg =>
      rw [decide_eq_false hct]
      rw [ha1f (by rw [← ha1]; simpa using hct)] at Hv
      simp only [Bool.not_false, ite_true, pure_ok, Except.ok.injEq] at Hv
      okRet
    rw [decide_eq_true hct]
    have hc2 := ha1t (by rw [← ha1]; simpa using hct)
    obtain ⟨a2, ha2, ha2t, ha2f⟩ := andM_ok hc2
    obtain ⟨l1, hl1, ha2⟩ := bind_ok ha2
    rw [ht, ok_bind, pure_ok, Except.ok.injEq] at ha2
    try wp_auto
    rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.inMem.TypeAssumptions.ptr_T_unfold.method_unfold]; try wp_auto
    wp_apply wp_T gx x t $$ [Hx] as %ut2 %Hut2
    · iframe Hx; ipureintro; exact ht
    try wp_auto
    rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.inMem.TypeAssumptions.ptr_ll1_unfold.method_unfold]; try wp_auto
    wp_apply wp_ll1 gx x l1 $$ [Hx] as %ul1 #Hul1
    · iframe Hx; ipureintro; exact hl1
    try wp_auto
    wp_apply wp_Has ul1 l1 ut2 $$ [Hul1]
    · iexact Hul1
    rw [Hut2]
    try iintro -
    cases hh : l1.has t with
    | false =>
      rw [ha2f (by rw [← ha2, hh])] at Hv
      simp only [Bool.not_false, ite_true, pure_ok, Except.ok.injEq] at Hv
      okRet
    | true =>
    have hc3 := ha2t (by rw [← ha2, hh])
    obtain ⟨cc, hcc, hc3⟩ := bind_ok hc3
    obtain ⟨lL, hlL, hc3⟩ := bind_ok hc3
    simp only [pure_ok, Except.ok.injEq] at hc3
    subst hc3
    try wp_auto
    rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.inMem.TypeAssumptions.ptr_c_unfold.method_unfold]; try wp_auto
    wp_apply wp_c gx x cc $$ [Hx] as %uc %Huc
    · iframe Hx; ipureintro; exact hcc
    try wp_auto
    rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.inMem.TypeAssumptions.ptr_L_unfold.method_unfold]; try wp_auto
    wp_apply wp_L gx x lL $$ [Hx] as %uL #HuL
    · iframe Hx; ipureintro; exact hlL
    ihave %HuLl := logRO_len _ _ $$ HuL
    try wp_auto
    rw [Huc, HuLl]
    by_cases hcl : cc ≤ lL.length
    · rw [decide_eq_true hcl]
      simp only [hcl, decide_true, Bool.not_true, Bool.false_eq_true, ite_false] at Hv
      okNext
    · rw [decide_eq_false hcl]
      simp only [hcl, decide_false, Bool.not_false, ite_true, pure_ok, Except.ok.injEq] at Hv
      okRet
  rename_i w
  iintro Hw
  icases Hw with (⟨%Hw, x, s, n, ev, «$res0»⟩ | ⟨%Hw, «$res0»⟩)
  rotate_left
  · obtain ⟨rfl, rfl⟩ := Hw
    try wp_auto
    iapply HΦ; ipureintro; trivial
  obtain ⟨rfl, Hv⟩ := Hw
  try wp_auto
  unfold InMem.okApp at Hv
  obtain ⟨ap, hap, Hv⟩ := bind_ok Hv
  wp_join (Q := fun w => iprop((⌜w = executeVal ∧ x.okTail = .ok v⌝ ∗ x_ptr ↦ gx ∗ s_ptr ↦ gx.s' ∗ n_ptr ↦ gx.n' ∗
      ev_ptr ↦ gx.ev' ∗ «$res0_ptr» ↦ zero_val Bool) ∨ (⌜w = returnVal #() ∧ v = false⌝ ∗ «$res0_ptr» ↦ false)))
    at next with [x s n ev «$res0»]
  · rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.inMem.TypeAssumptions.ptr_app_unfold.method_unfold]; try wp_auto
    wp_apply wp_app gx x ap $$ [Hx]
    · iframe Hx; ipureintro; exact hap
    try iintro -
    cases ap with
    | false =>
      simp only [Bool.false_eq_true, ite_false] at Hv
      okNext
    | true =>
    simp only [ite_true] at Hv
    try wp_auto
    -- `ev.has(FFirst)`: the first index the leader reports
    wp_join (Q := fun w => iprop((⌜w = executeVal ∧ x.okEs = .ok v⌝ ∗ x_ptr ↦ gx ∗ s_ptr ↦ gx.s' ∗ n_ptr ↦ gx.n' ∗
        ev_ptr ↦ gx.ev' ∗ «$res0_ptr» ↦ zero_val Bool) ∨ (⌜w = returnVal #() ∧ v = false⌝ ∗ «$res0_ptr» ↦ false)))
      at next with [x s n ev «$res0»]
    · rw [show (github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.FFirst : val) = #fFirst from rfl]
      try wp_auto
      wp_apply wp_has gx.ev' x.ev fFirst x.ev.first.isSome $$ [He]
      · iframe He; ipureintro; exact Event.hasF_First _
      try iintro -
      cases hfs : x.ev.first.isSome with
      | false =>
        simp only [hfs, Bool.false_eq_true, ite_false] at Hv
        okNext
      | true =>
      simp only [hfs, ite_true] at Hv
      try wp_auto
      obtain ⟨f, hf, Hv⟩ := bind_ok Hv
      obtain ⟨l1, hl1, Hv⟩ := bind_ok Hv
      obtain ⟨t, ht, Hv⟩ := bind_ok Hv
      obtain ⟨g1, hg1, Hv⟩ := bind_ok Hv
      have hg1w := InMem.ll1_get_within HW HN hl1 hg1
      wp_apply wp_first gx.ev' x.ev f $$ [He] as %uf %Huf
      · iframe He; ipureintro; exact hf
      try wp_auto
      rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.inMem.TypeAssumptions.ptr_T_unfold.method_unfold]; try wp_auto
      wp_apply wp_T gx x t $$ [Hx] as %ut %Hut
      · iframe Hx; ipureintro; exact ht
      try wp_auto
      rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.inMem.TypeAssumptions.ptr_ll1_unfold.method_unfold]; try wp_auto
      wp_apply wp_ll1 gx x l1 $$ [Hx] as %ul1 #Hul1
      · iframe Hx; ipureintro; exact hl1
      try wp_auto
      wp_apply wp_Get ul1 l1 ut g1 $$ [Hul1] as %ug #Hug
      · iframe Hul1; ipureintro; rw [Hut]; exact hg1
      ihave %Hugl := logRO_len _ _ $$ Hug
      try wp_auto
      have hg1l := hg1w.1
      rw [decide_w64_eq, Huf, sint_add_one (by rw [Hugl]; omega), Hugl]
      by_cases hfe : f = (g1.length : Int) + 1
      · rw [decide_eq_true hfe]
        simp only [hfe, bne_self_eq_false, Bool.false_eq_true, ite_false] at Hv
        okNext
      · rw [decide_eq_false hfe]
        simp only [show (f != (g1.length : Int) + 1) = true by simpa using hfe, ite_true, pure_ok, Except.ok.injEq] at Hv
        okRet
    rename_i w
    iintro Hw
    icases Hw with (⟨%Hw, x, s, n, ev, «$res0»⟩ | ⟨%Hw, «$res0»⟩)
    rotate_left
    · obtain ⟨rfl, rfl⟩ := Hw
      try wp_auto
      iright; iframe; ipureintro; exact ⟨rfl, rfl⟩
    obtain ⟨rfl, Hv⟩ := Hw
    try wp_auto
    unfold InMem.okEs at Hv
    obtain ⟨es, hes, Hv⟩ := bind_ok Hv
    obtain ⟨r1, hr1, Hv⟩ := bind_ok Hv
    have hesw := InMem.es_within HN HC hes
    rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.inMem.TypeAssumptions.ptr_es_unfold.method_unfold]; try wp_auto
    wp_apply wp_es gx x es $$ [Hx] as %ue #Hue
    · iframe Hx; ipureintro; exact hes
    ihave %Huel := logRO_len _ _ $$ Hue
    ihave #Hue' := Hue
    iunfold logRO at Hue'
    icases Hue' with ⟨%ges, #Hges, #Hgb⟩
    try wp_auto
    ihave IH : iprop(∃ (qv : w64), "q" ∷ q_ptr ↦ qv ∗
        "%Hq" ∷ ⌜1 ≤ sint.Z qv ∧ sint.Z qv ≤ es.length + 1 ∧
          anyM (es.drop (sint.Z qv - 1).toNat) (fun e => do pure (e.term != (← x.T))) = .ok r1⌝) $$ [q]
    · iexists _; iframe; ipureintro
      refine ⟨by rw [sint_one]; omega, by rw [sint_one]; omega, by simpa using hr1⟩
    wp_for IH
    obtain ⟨hq0, hq1, hqS⟩ := Hq
    try wp_auto
    ihave %Hgel := ownSlice_len $$ Hges
    ihave %Hgbl := BigSepL2.bigSepL2_length $$ Hgb
    wp_if_destruct
    · -- `q <= len(es)`: entry `q - 1`
      rw [Huel] at Hif
      have hk : sint.Z (qv - W64 1) = sint.Z qv - 1 := sint_sub_one hq0
      have hj : (sint.Z qv - 1).toNat < es.length := by omega
      rw [List.drop_eq_getElem_cons hj, anyM_cons] at hqS
      obtain ⟨cq, hcq, hqS⟩ := bind_ok hqS
      obtain ⟨tq, htq, hcq⟩ := bind_ok hcq
      simp only [pure_ok, Except.ok.injEq] at hcq
      subst hcq
      try wp_auto
      rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z (qv - W64 1) ∧
        sint.Z (qv - W64 1) < sint.Z ue.len from by rw [hk, Huel]; constructor <;> omega))]
      obtain ⟨ge, Hge⟩ : ∃ e, ges[(sint.Z (qv - W64 1)).toNat]? = some e :=
        ⟨_, List.getElem?_eq_getElem (by rw [hk, Hgbl]; omega)⟩
      have Hxe : es[(sint.Z (qv - W64 1)).toNat]? = some es[(sint.Z qv - 1).toNat] := by
        rw [hk]; exact List.getElem?_eq_getElem hj
      ihave #Hex := BigSepL2.bigSepL2_lookup (Φ := fun _ e x => entryRO (GF := GF) e x) Hge Hxe $$ Hgb
      iunfold entryRO at Hex
      icases Hex with ⟨%Hex, -⟩
      icases ownSlice_elem_acc _ ge ue _ ges (by rw [hk]; omega) Hge $$ Hges with ⟨He', -⟩
      icases typedPointsto_split _ _ _ $$ He' with Hef
      simp only [TypedPointsto.typedPointstoDef]
      iNamed Hef
      try wp_auto
      rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.inMem.TypeAssumptions.ptr_T_unfold.method_unfold]; try wp_auto
      wp_apply wp_T gx x tq $$ [Hx] as %ut %Hut
      · iframe Hx; ipureintro; exact htq
      try wp_auto
      rw [decide_w64_eq, Hex.1, Hut]
      by_cases hte : es[(sint.Z qv - 1).toNat].term = tq
      · rw [show (sint.Z (qv - W64 1)).toNat = (sint.Z qv - 1).toNat by rw [hk]] at *
        rw [decide_eq_true hte]
        simp only [hte, bne_self_eq_false, Bool.false_eq_true, ite_false] at hqS
        try wp_auto
        wp_for_post
        iframe
        iexists _
        iframe
        ipureintro
        have hesl := hesw.1
        have hq' : sint.Z (qv + W64 1) = sint.Z qv + 1 := sint_add_one (by omega)
        rw [hq']
        refine ⟨by omega, by omega, ?_⟩
        rw [show (sint.Z qv + 1 - 1).toNat = (sint.Z qv - 1).toNat + 1 by omega]
        exact hqS
      · rw [show (sint.Z (qv - W64 1)).toNat = (sint.Z qv - 1).toNat by rw [hk]] at *
        rw [decide_eq_false hte]
        simp only [show (es[(sint.Z qv - 1).toNat].term != tq) = true by simpa using hte, ite_true,
          pure_ok, Except.ok.injEq] at hqS
        subst hqS
        simp only [ite_true, pure_ok, Except.ok.injEq] at Hv
        try wp_auto
        wp_for_post
        okRet
    -- the loop's end: no entry of another term
    rw [Huel] at Hif
    have hqk : sint.Z qv = es.length + 1 := by omega
    rw [hqk, show ((es.length : Int) + 1 - 1).toNat = es.length by omega, List.drop_eq_nil_of_le (by simp)] at hqS
    simp only [anyM, pure_ok, Except.ok.injEq] at hqS
    subst hqS
    simp only [Bool.false_eq_true, ite_false] at Hv
    obtain ⟨bad, hbad, Hv⟩ := bind_ok Hv
    have hesl := hesw.1
    try wp_auto
    ihave IH2 : iprop(∃ (qv : w64), "q" ∷ q_ptr ↦ qv ∗
        "%Hq" ∷ ⌜1 ≤ sint.Z qv ∧ sint.Z qv ≤ es.length + 1 ∧
          anyM ((List.range es.length).drop (sint.Z qv - 1).toNat) (x.okBad es) = .ok bad⌝) $$ [q]
    · iexists _; iframe; ipureintro
      refine ⟨by rw [sint_one]; omega, by rw [sint_one]; omega, by simpa using hbad⟩
    wp_for IH2
    obtain ⟨hq0, hq1, hqS⟩ := Hq
    try wp_auto
    wp_if_destruct
    · rw [Huel] at Hif
      have hk : sint.Z (qv - W64 1) = sint.Z qv - 1 := sint_sub_one hq0
      have hj : (sint.Z qv - 1).toNat < es.length := by omega
      rw [List.drop_eq_getElem_cons (by simpa using hj), anyM_cons] at hqS
      simp only [List.getElem_range] at hqS
      obtain ⟨cq, hcq, hqS⟩ := bind_ok hqS
      have hkn : sint.nat (qv - W64 1) = (sint.Z qv - 1).toNat := by rw [← hk]
      icases sliceRO_at (fun g e => entryRO (GF := GF) g e) ue ges es (qv - W64 1) ⟨by omega, by omega⟩ $$ [Hges Hgb] with ⟨%ge, #Hgea, #Hge⟩
      · iframe Hges Hgb
      rw [hkn] at *
      try wp_auto
      wp_apply wp_load_at _ _ _ (by omega) $$ [Hgea]
      · iexact Hgea
      try iintro -
      try wp_auto
      wp_apply wp_IsConf ge _ $$ [Hge]
      · iexact Hge
      try iintro -
      unfold InMem.okBad at hcq
      cases hic : isConf es[(sint.Z qv - 1).toNat]! with
      | false =>
        simp only [hic, Bool.not_false, ite_true, pure_ok, Except.ok.injEq] at hcq
        subst hcq
        simp only [Bool.false_eq_true, ite_false] at hqS
        try wp_auto
        wp_for_post
        iframe
        iexists _
        iframe
        ipureintro
        have hq' : sint.Z (qv + W64 1) = sint.Z qv + 1 := sint_add_one (by omega)
        rw [hq']
        refine ⟨by omega, by omega, ?_⟩
        rw [show (sint.Z qv + 1 - 1).toNat = (sint.Z qv - 1).toNat + 1 by omega]
        exact hqS
      | true =>
      simp only [hic, Bool.not_true, Bool.false_eq_true, ite_false] at hcq
      obtain ⟨l1, hl1, hcq⟩ := bind_ok hcq
      obtain ⟨t, ht, hcq⟩ := bind_ok hcq
      obtain ⟨g1, hg1, hcq⟩ := bind_ok hcq
      obtain ⟨sw, hsw, hcq⟩ := bind_ok hcq
      have hg1w := InMem.ll1_get_within HW HN hl1 hg1
      have hcab : bigOk x.s.confAt[x.n]! :=
        HW.confAt _ (getElem!_mem (show x.n < x.s.confAt.length by rw [HWf.len_confAt]; exact Hnl))
      unfold bigOk at hcab
      try wp_auto
      rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.inMem.TypeAssumptions.ptr_T_unfold.method_unfold]; try wp_auto
      wp_apply wp_T gx x t $$ [Hx] as %ut %Hut
      · iframe Hx; ipureintro; exact ht
      try wp_auto
      rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.inMem.TypeAssumptions.ptr_ll1_unfold.method_unfold]; try wp_auto
      wp_apply wp_ll1 gx x l1 $$ [Hx] as %ul1 #Hul1
      · iframe Hx; ipureintro; exact hl1
      try wp_auto
      wp_apply wp_Get ul1 l1 ut g1 $$ [Hul1] as %ug #Hug
      · iframe Hul1; ipureintro; rw [Hut]; exact hg1
      try wp_auto
      wp_apply wp_AllSwitched gx.s' x.s gx.n' ug g1 sw $$ [Hs Hug]
      · iframe Hs Hug; ipureintro; rw [hnn]; exact ⟨hn0, hnl, hsw, by omega, by have := hg1w.1; omega⟩
      try iintro -
      cases sw with
      | false =>
        simp only [Bool.not_false, ite_true, pure_ok, Except.ok.injEq] at hcq
        subst hcq
        simp only [ite_true, pure_ok, Except.ok.injEq] at hqS
        subst hqS
        simp only [ite_true, pure_ok, Except.ok.injEq] at Hv
        try wp_auto
        wp_for_post
        okRet
      | true =>
      simp only [Bool.not_true, Bool.false_eq_true, ite_false] at hcq
      try wp_auto
      ihave IH3 : iprop(∃ (rv : w64), "r" ∷ r_ptr ↦ rv ∗
          "%Hr" ∷ ⌜1 ≤ sint.Z rv ∧ sint.Z rv ≤ sint.Z qv ∧
            ∀ j, j < (sint.Z rv - 1).toNat → isConf es[j]! = false⌝) $$ [r]
      · iexists _; iframe; ipureintro
        refine ⟨by rw [sint_one]; omega, by rw [sint_one]; omega, fun j hj => by rw [sint_one] at hj; simp at hj⟩
      wp_for IH3
      obtain ⟨hr0, hr1, hrS⟩ := Hr
      try wp_auto
      rw [hk]
      wp_if_destruct
      · have hk2 : sint.Z (rv - W64 1) = sint.Z rv - 1 := sint_sub_one hr0
        have hkn2 : sint.nat (rv - W64 1) = (sint.Z rv - 1).toNat := by rw [← hk2]
        icases sliceRO_at (fun g e => entryRO (GF := GF) g e) ue ges es (rv - W64 1) ⟨by omega, by omega⟩ $$ [Hges Hgb] with ⟨%ge2, #Hgea2, #Hge2⟩
        · iframe Hges Hgb
        rw [hkn2] at *
        try wp_auto
        wp_apply wp_load_at _ _ _ (by omega) $$ [Hgea2]
        · iexact Hgea2
        try iintro -
        try wp_auto
        wp_apply wp_IsConf ge2 _ $$ [Hge2]
        · iexact Hge2
        try iintro -
        cases hic2 : isConf es[(sint.Z rv - 1).toNat]! with
        | false =>
          try wp_auto
          wp_for_post
          iframe
          iexists _
          iframe
          ipureintro
          have hr' : sint.Z (rv + W64 1) = sint.Z rv + 1 := sint_add_one (by omega)
          rw [hr']
          refine ⟨by omega, by omega, fun j hj => ?_⟩
          by_cases hjj : j < (sint.Z rv - 1).toNat
          · exact hrS j hjj
          · rw [show j = (sint.Z rv - 1).toNat by omega]; exact hic2
        | true =>
        have hany : ((List.range (sint.Z qv - 1).toNat).any fun r => isConf es[r]!) = true :=
          List.any_eq_true.mpr ⟨(sint.Z rv - 1).toNat, List.mem_range.mpr (by omega), hic2⟩
        simp only [hany, ite_true, pure_ok, Except.ok.injEq] at hcq
        subst hcq
        simp only [ite_true, pure_ok, Except.ok.injEq] at hqS
        subst hqS
        simp only [ite_true, pure_ok, Except.ok.injEq] at Hv
        try wp_auto
        wp_for_post
        try wp_auto
        wp_for_post
        okRet
      have hrq : sint.Z rv = sint.Z qv := by omega
      have hnone : ((List.range (sint.Z qv - 1).toNat).any fun r => isConf es[r]!) = false := by
        rw [List.any_eq_false]
        intro j hj
        rw [hrS j (by rw [hrq]; exact List.mem_range.mp hj)]
        simp
      simp only [hnone, Bool.false_eq_true, ite_false] at hcq
      try wp_auto
      wp_apply wp_load_at _ _ _ hn0 $$ [Hcfa]
      · iexact Hcfa
      try iintro -
      try wp_auto
      rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z (qv - W64 1) ∧
        sint.Z (qv - W64 1) < sint.Z ue.len from by rw [hk, Huel]; constructor <;> omega))]
      obtain ⟨ge3, Hge3⟩ : ∃ e, ges[(sint.Z (qv - W64 1)).toNat]? = some e :=
        ⟨_, List.getElem?_eq_getElem (by rw [hk, Hgbl]; omega)⟩
      have Hxe3 : es[(sint.Z (qv - W64 1)).toNat]? = some es[(sint.Z qv - 1).toNat]! := by
        rw [hk, List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hj]; rfl
      ihave #Hex3 := BigSepL2.bigSepL2_lookup (Φ := fun _ e x => entryRO (GF := GF) e x) Hge3 Hxe3 $$ Hgb
      iunfold entryRO at Hex3
      icases Hex3 with ⟨%-, #Hval⟩
      icases ownSlice_elem_acc _ ge3 ue _ ges (by rw [hk]; omega) Hge3 $$ Hges with ⟨He3, -⟩
      icases typedPointsto_split _ _ _ $$ He3 with Hef3
      simp only [TypedPointsto.typedPointstoDef]
      iNamed Hef3
      try wp_auto
      obtain ⟨lg, hlg, hcq⟩ := bind_ok hcq
      simp only [pure_ok, Except.ok.injEq] at hcq
      have hcw := HW.config _ (getElem!_mem (show x.n < x.s.config.length by rw [HWf.len_config]; exact Hnl))
      have heb : es[(sint.Z qv - 1).toNat]!.chgSize ≤ EE :=
        (hesw.2 _ (getElem!_mem hj)).2
      have hlb := legal_bounds (w := x.ev.weight) hcw heb hEE
      wp_apply wp_Legal cfv _ ge3.Value' _ lg $$ [Hcf Hval]
      · iframe Hcf Hval; ipureintro; exact ⟨hlg, hlb⟩
      try iintro -
      cases lg with
      | false =>
        subst hcq
        simp only [Bool.not_false, ite_true, pure_ok, Except.ok.injEq] at hqS
        subst hqS
        simp only [ite_true, pure_ok, Except.ok.injEq] at Hv
        try wp_auto
        wp_for_post
        okRet
      | true =>
      subst hcq
      simp only [Bool.not_true, Bool.false_eq_true, ite_false] at hqS
      try wp_auto
      wp_for_post
      iframe
      iexists _
      iframe
      ipureintro
      have hq' : sint.Z (qv + W64 1) = sint.Z qv + 1 := sint_add_one (by omega)
      rw [hq']
      refine ⟨by omega, by omega, ?_⟩
      rw [show (sint.Z qv + 1 - 1).toNat = (sint.Z qv - 1).toNat + 1 by omega]
      exact hqS
    · rw [Huel] at Hif
      have hqk : sint.Z qv = es.length + 1 := by omega
      rw [hqk, show ((es.length : Int) + 1 - 1).toNat = es.length by omega,
        List.drop_eq_nil_of_le (by simp)] at hqS
      simp only [anyM, pure_ok, Except.ok.injEq] at hqS
      subst hqS
      simp only [Bool.false_eq_true, ite_false] at Hv
      okNext
  rename_i w
  iintro Hw
  icases Hw with (⟨%Hw, x, s, n, ev, «$res0»⟩ | ⟨%Hw, «$res0»⟩)
  rotate_left
  · obtain ⟨rfl, rfl⟩ := Hw
    try wp_auto
    iapply HΦ; ipureintro; trivial
  obtain ⟨rfl, Hv⟩ := Hw
  try wp_auto
  unfold InMem.okTail at Hv
  obtain ⟨c0, hc0, Hv⟩ := bind_ok Hv
  obtain ⟨ld, hld, hldt, hldf⟩ := andM_ok hc0
  rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.inMem.TypeAssumptions.ptr_leads_unfold.method_unfold]; try wp_auto
  wp_apply wp_leads gx x ld $$ [Hx]
  · iframe Hx; ipureintro; exact hld
  try iintro -
  cases ld with
  | false =>
    rw [hldf rfl] at Hv
    simp only [Bool.false_eq_true, ite_false, pure_ok, Except.ok.injEq] at Hv
    subst Hv
    try wp_auto
    iapply HΦ; ipureintro; trivial
  | true =>
  obtain ⟨cc, hcc, hc0'⟩ := bind_ok (hldt rfl)
  simp only [pure_ok, Except.ok.injEq] at hc0'
  try wp_auto
  rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.inMem.TypeAssumptions.ptr_c_unfold.method_unfold]; try wp_auto
  wp_apply wp_c gx x cc $$ [Hx] as %uc %Huc
  · iframe Hx; ipureintro; exact hcc
  try wp_auto
  rw [Huc, sint_zero]
  by_cases hcp : cc > 0
  case neg =>
    rw [decide_eq_false hcp]
    rw [← hc0', decide_eq_false hcp] at Hv
    simp only [Bool.false_eq_true, ite_false, pure_ok, Except.ok.injEq] at Hv
    subst Hv
    try wp_auto
    iapply HΦ; ipureintro; trivial
  rw [decide_eq_true hcp]
  rw [← hc0', decide_eq_true hcp] at Hv
  simp only [ite_true] at Hv
  obtain ⟨cm, hcm, Hv⟩ := bind_ok Hv
  try wp_auto
  rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.inMem.TypeAssumptions.ptr_cmt_unfold.method_unfold]; try wp_auto
  wp_apply wp_cmt gx x cm $$ [Hx]
  · iframe Hx; ipureintro; exact hcm
  try iintro -
  cases cm with
  | true =>
    simp only [ite_true] at Hv
    obtain ⟨t, ht, Hv⟩ := bind_ok Hv
    rw [hcc, ok_bind] at Hv
    obtain ⟨lc, hlc, Hv⟩ := bind_ok Hv
    rw [ht, ok_bind] at Hv
    obtain ⟨cf, hcf, Hv⟩ := bind_ok Hv
    simp only [pure_ok, Except.ok.injEq] at Hv
    subst Hv
    try wp_auto
    rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.inMem.TypeAssumptions.ptr_T_unfold.method_unfold]; try wp_auto
    wp_apply wp_T gx x t $$ [Hx] as %ut %Hut
    · iframe Hx; ipureintro; exact ht
    try wp_auto
    rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.inMem.TypeAssumptions.ptr_c_unfold.method_unfold]; try wp_auto
    wp_apply wp_c gx x cc $$ [Hx] as %uc2 %Huc2
    · iframe Hx; ipureintro; exact hcc
    try wp_auto
    have hsrv : (x.s.cfg.server.length : Int) < 2 ^ 61 := HW.cfg.1
    wp_apply wp_Acked gx.s' x.s gx.n' ut uc2 $$ [Hs] as %uak #Hak
    · iframe Hs; ipureintro; exact ⟨hn0, hnl, hsrv⟩
    rw [hnn, Hut, Huc2]
    try wp_auto
    rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.inMem.TypeAssumptions.ptr_T_unfold.method_unfold]; try wp_auto
    wp_apply wp_T gx x t $$ [Hx] as %ut2 %Hut2
    · iframe Hx; ipureintro; exact ht
    try wp_auto
    rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.inMem.TypeAssumptions.ptr_lc1_unfold.method_unfold]; try wp_auto
    wp_apply wp_lc1 gx x lc $$ [Hx] as %ulc #Hulc
    · iframe Hx; ipureintro; exact hlc
    try wp_auto
    wp_apply wp_ConfGet ulc lc ut2 cf $$ [Hulc] as %ucf #Hucf
    · iframe Hulc; ipureintro; rw [Hut2]; exact hcf
    try wp_auto
    have hakl := State.acked_length_le x.s x.n t cc
    have hcl := confWithin_lt (w := x.ev.weight) (InMem.lc1_get_within HW hlc hcf) hEE
    wp_apply wp_IsQuorum uak _ ucf _ $$ [Hak Hucf]
    · iframe Hak Hucf; ipureintro; exact ⟨by omega, hcl.1, hcl.2⟩
    try iintro -
    try wp_auto
    iapply HΦ; ipureintro; trivial
  | false =>
  simp only [Bool.false_eq_true, ite_false] at Hv
  obtain ⟨lL, hlL, Hv⟩ := bind_ok Hv
  rw [hcc, ok_bind] at Hv
  obtain ⟨t, ht, Hv⟩ := bind_ok Hv
  try wp_auto
  rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.inMem.TypeAssumptions.ptr_L_unfold.method_unfold]; try wp_auto
  wp_apply wp_L gx x lL $$ [Hx] as %uL #HuL
  · iframe Hx; ipureintro; exact hlL
  try wp_auto
  rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.inMem.TypeAssumptions.ptr_c_unfold.method_unfold]; try wp_auto
  wp_apply wp_c gx x cc $$ [Hx] as %uc2 %Huc2
  · iframe Hx; ipureintro; exact hcc
  try wp_auto
  rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.inMem.TypeAssumptions.ptr_T_unfold.method_unfold]; try wp_auto
  wp_apply wp_T gx x t $$ [Hx] as %ut %Hut
  · iframe Hx; ipureintro; exact ht
  try wp_auto
  wp_apply wp_RecordedIn g.Chain' x.s.chain g.TermLen' x.s.termLen uL lL uc2 ut v $$ [HChain HTermLen HuL]
  · iframe HChain HTermLen HuL; ipureintro; rw [Huc2, Hut]; exact Hv
  try iintro -
  try wp_auto
  iapply HΦ; ipureintro; trivial

end proof

end AntCheck
end EtcdGrove
end Perennial

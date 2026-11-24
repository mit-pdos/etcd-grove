/-
Lean-first (no Rocq counterpart). #33 S3b W2 (2026-11-23): the proof of `State.Recv` (B 196-210).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State__Recv
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State__clone
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Event__msg
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Msg__to
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Msg__term
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.IsReq
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.SnapOk
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.ReqFactIn
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State__Sendable
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.setMsgs
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.StateLaws
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.EvalLaws
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.OnDiskLaws

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

theorem State.Recv.wp_proof
    (wp_clone : State.clone.spec (GF := GF) (hG := hG))
    (wp_msg : Event.msg.spec (GF := GF) (hG := hG))
    (wp_to : Msg.to.spec (GF := GF) (hG := hG))
    (wp_term : Msg.term.spec (GF := GF) (hG := hG))
    (wp_IsReq : IsReq.spec (GF := GF) (hG := hG))
    (wp_SnapOk : SnapOk.spec (GF := GF) (hG := hG))
    (wp_ReqFactIn : ReqFactIn.spec (GF := GF) (hG := hG))
    (wp_Sendable : State.Sendable.spec (GF := GF) (hG := hG))
    (wp_setMsgs : setMsgs.spec (GF := GF) (hG := hG)) :
    State.Recv.spec (GF := GF) (hG := hG) := by
  intro p s n e ev o
  wp_start as ⟨#Hs, #He, %Hn, %Hlt, %HBd, %Ho⟩
  ihave #Hs' := Hs
  iunfold stateRO at Hs'
  iNamed Hs'
  iNamed Hf
  iStructNamed Hp

  obtain ⟨bb, EE, HW, HNO, -, hbb, -⟩ := HBd
  unfold numBound Event.weight at hbb
  unfold State.recv at Ho
  obtain ⟨m, hm, Ho⟩ := bind_ok Ho
  have hmn : m.NumsOk := HNO.2.2.2.2.2.2.2.2.2.2.2.1 m (need_ok hm)
  have hms : m.size ≤ ev.size := by unfold Event.size; rw [need_ok hm]; simp; omega
  iunfold configRO at HCfg
  icases HCfg with ⟨%gc, #Hgc, #Hsrv, #-, %-⟩
  iStructNamed Hgc
  ihave #Hme := strsRO_at gc.Server' s.cfg.server n ⟨Hn, Hlt⟩ $$ Hsrv
  wp_auto
  wp_apply wp_msg e ev m $$ [He] as %gm #Hm
  · iframe He; ipureintro; exact hm
  try wp_auto
  obtain ⟨dst, hdst, Ho⟩ := bind_ok Ho
  rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Msg.TypeAssumptions.ptr_to_unfold.method_unfold]
  try wp_auto
  wp_apply wp_to gm m dst $$ [Hm]
  · iframe Hm; ipureintro; exact hdst
  try wp_auto
  wp_apply wp_load_at _ _ _ Hn $$ [Hme] as -
  · iexact Hme
  try wp_auto
  by_cases hd : dst = s.cfg.server[sint.nat n]!
  case neg =>
    rw [decide_eq_false hd]
    rw [show (dst != s.cfg.server[sint.nat n]!) = true by simpa using hd] at Ho
    simp only [ite_true, pure_ok, Except.ok.injEq] at Ho
    subst Ho
    try wp_auto
    iapply HΦ; iunfold succOwn; ipureintro; rfl
  rw [decide_eq_true hd]
  rw [show (dst != s.cfg.server[sint.nat n]!) = false by simpa using hd] at Ho
  simp only [Bool.false_eq_true, ite_false] at Ho
  try wp_auto
  wp_apply wp_clone p s $$ [Hs] as %q Hq
  · iexact Hs
  try wp_auto
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %sl1 ⟨Hsl1, -⟩
  imod ownSlice_persist $$ Hsl1 with #Hsl1
  try wp_auto
  wp_apply wp_setMsgs g.Pending' s.pending n _ [m] $$ [HPending Hsl1 Hm] as %out #Hout
  · iframe HPending
    isplitl
    · iunfold msgsRO; iexists [gm]; iframe Hsl1
      iapply BigSepL2.bigSepL2_cons.2; iframe Hm; iapply BigSepL2.bigSepL2_nil.2; iempintro
    ipureintro; exact ⟨Hn, by rw [HWf.len_pending]; exact Hlt⟩
  try wp_auto
  wp_apply wp_set_pending q s out (s.pending.set (sint.nat n) [m]) (by rw [List.length_set, HWf.len_pending]) $$ [Hq Hout] as Hq
  · iframe Hq Hout
  try wp_auto
  -- `IsReq(m) && m.term() >= s.CurrentTerm[n]`
  obtain ⟨c, hc, Ho⟩ := bind_ok Ho
  obtain ⟨rq, hrq, ht1, hf1⟩ := andM_ok hc
  wp_apply wp_IsReq gm m rq $$ [Hm]
  · iframe Hm; ipureintro; exact hrq
  cases rq
  · rw [hf1 rfl] at Ho
    simp only [Bool.false_eq_true, ite_false, pure_ok, Except.ok.injEq] at Ho
    subst Ho
    try wp_auto
    iapply HΦ
    iunfold succOwn
    isplitr
    · ipureintro; rfl
    iexact Hq
  have hc2 := ht1 rfl
  obtain ⟨mt, hmt, hc2⟩ := bind_ok hc2
  simp only [pure_ok, Except.ok.injEq] at hc2
  subst hc2
  try wp_auto
  rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Msg.TypeAssumptions.ptr_term_unfold.method_unfold]
  try wp_auto
  wp_apply wp_term gm m mt $$ [Hm] as %ut %Hut
  · iframe Hm; ipureintro; exact hmt
  try wp_auto
  icases intsRO_at g.CurrentTerm' s.currentTerm n ⟨Hn, by rw [HWf.len_currentTerm]; exact Hlt⟩ $$ HCurrentTerm with ⟨%ct, #Hcta, %Hct⟩
  wp_apply wp_load_at _ _ ct Hn $$ [Hcta]
  · iexact Hcta
  try wp_auto
  rw [Hut, Hct]
  by_cases hge : s.currentTerm[sint.nat n]! ≤ mt
  case neg =>
    rw [decide_eq_false hge]
    have : decide (mt ≥ s.currentTerm[sint.nat n]!) = false := by simpa using hge
    rw [this] at Ho
    simp only [Bool.false_eq_true, ite_false, pure_ok, Except.ok.injEq] at Ho
    subst Ho
    try wp_auto
    iapply HΦ
    iunfold succOwn
    isplitr
    · ipureintro; rfl
    iexact Hq
  rw [decide_eq_true hge]
  have : decide (mt ≥ s.currentTerm[sint.nat n]!) = true := by simpa using hge
  rw [this] at Ho
  simp only [ite_true] at Ho
  -- `SnapOk(s.LedLog, m) && s.Sendable(ReqFactIn(s.LedLog, m))`
  obtain ⟨c2, hc2, Ho⟩ := bind_ok Ho
  obtain ⟨so, hso, ht2, hf2⟩ := andM_ok hc2
  try wp_auto
  wp_apply wp_SnapOk g.LedLog' s.ledLog gm m so $$ [HLedLog Hm]
  · iframe HLedLog Hm; ipureintro; exact hso
  cases so
  · rw [hf2 rfl] at Ho
    simp only [Bool.not_false, ite_true, pure_ok, Except.ok.injEq] at Ho
    subst Ho
    try wp_auto
    iapply HΦ; iunfold succOwn; ipureintro; rfl
  have hc3 := ht2 rfl
  obtain ⟨f, hf, hc3⟩ := bind_ok hc3
  have hfw := reqFactIn_within (b := bb + ev.size) (E := EE) ⟨hmn, by omega⟩
    (fun p hp => ⟨(HW.2.2.2.2.2.2.2.2.2.2.2.2.1 p hp).1, logWithin.mono (by omega) (Nat.le_refl _) (HW.2.2.2.2.2.2.2.2.2.2.2.2.1 p hp).2⟩) hf
  unfold numOk numBound at hfw
  try wp_auto
  wp_apply wp_ReqFactIn g.LedLog' s.ledLog gm m f $$ [HLedLog Hm] as %gf #Hgf
  · iframe HLedLog Hm; ipureintro; exact hf
  try wp_auto
  wp_apply wp_Sendable p s gf f c2 $$ [Hs Hgf]
  · iframe Hs Hgf; ipureintro; exact ⟨hc3, by unfold bigOk; omega, by omega⟩
  cases c2
  · simp only [Bool.not_false, ite_true, pure_ok, Except.ok.injEq] at Ho
    subst Ho
    try wp_auto
    iapply HΦ; iunfold succOwn; ipureintro; rfl
  simp only [Bool.not_true, Bool.false_eq_true, ite_false, pure_ok, Except.ok.injEq] at Ho
  subst Ho
  try wp_auto
  iapply HΦ
  iunfold succOwn
  isplitr
  · ipureintro; rfl
  iexact Hq

end proof

end AntCheck
end EtcdGrove
end Perennial

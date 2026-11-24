/-
Lean-first (no Rocq counterpart). #33 S3b W6 (2026-11-23): the proof of `State.Mem` (B 450-459).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State__Mem
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State__InMemory
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State__clone
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State__queued
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Event__w
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.setQueue
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

theorem State.Mem.wp_proof (inMemory_lengths : W6Laws.InMemoryLengths)
    (wp_InMemory : State.InMemory.spec (GF := GF) (hG := hG))
    (wp_clone : State.clone.spec (GF := GF) (hG := hG))
    (wp_queued : State.queued.spec (GF := GF) (hG := hG))
    (wp_w : Event.w.spec (GF := GF) (hG := hG))
    (wp_setQueue : setQueue.spec (GF := GF) (hG := hG)) :
    State.Mem.spec (GF := GF) (hG := hG) := by
  intro p s n e ev o
  wp_start as ⟨#Hs, #He, %Hn, %Hlt, %HBd, %Ho⟩
  ihave #Hs' := Hs
  iunfold stateRO at Hs'
  iNamed Hs'
  iNamed Hf
  iStructNamed Hp
  unfold State.mem at Ho
  obtain ⟨r, hr, Ho⟩ := bind_ok Ho
  obtain ⟨hrl, hcl, hal⟩ := inMemory_lengths _ _ _ _ hr
  have HBd' := HBd
  obtain ⟨bb, EE, HW, HNO, -, hbb, -⟩ := HBd'
  unfold numBound Event.weight at hbb
  iapply wp_fupd
  wp_auto
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
  try wp_auto
  wp_apply wp_clone p s $$ [Hs] as %q Hq
  · iexact Hs
  try wp_auto
  wp_apply wp_set_role q s _ _ (by rw [hrl, HWf.len_role]) $$ [Hq HrRole] as Hq
  · iframe Hq HrRole
  try wp_auto
  wp_apply wp_set_leaders q ({ s with role := r.role } : State) _ _  $$ [Hq HrLeaders] as Hq
  · iframe Hq HrLeaders
  try wp_auto
  wp_apply wp_set_ledLog q ({ s with role := r.role, leaders := r.leaders } : State) _ _  $$ [Hq HrLedLog] as Hq
  · iframe Hq HrLedLog
  try wp_auto
  wp_apply wp_set_ledConf q ({ s with role := r.role, leaders := r.leaders, ledLog := r.ledLog } : State) _ _  $$ [Hq HrLedConf] as Hq
  · iframe Hq HrLedConf
  try wp_auto
  wp_apply wp_set_ledAt q ({ s with role := r.role, leaders := r.leaders, ledLog := r.ledLog, ledConf := r.ledConf } : State) _ _  $$ [Hq HrLedAt] as Hq
  · iframe Hq HrLedAt
  try wp_auto
  wp_apply wp_set_elAt q ({ s with role := r.role, leaders := r.leaders, ledLog := r.ledLog, ledConf := r.ledConf, ledAt := r.ledAt } : State) _ _  $$ [Hq HrElAt] as Hq
  · iframe Hq HrElAt
  try wp_auto
  wp_apply wp_set_config q ({ s with role := r.role, leaders := r.leaders, ledLog := r.ledLog, ledConf := r.ledConf, ledAt := r.ledAt, elAt := r.elAt } : State) _ _ (by rw [hcl, HWf.len_config]) $$ [Hq HrConfig] as Hq
  · iframe Hq HrConfig
  try wp_auto
  wp_apply wp_set_confAt q ({ s with role := r.role, leaders := r.leaders, ledLog := r.ledLog, ledConf := r.ledConf, ledAt := r.ledAt, elAt := r.elAt, config := r.config } : State) _ _ (by rw [hal, HWf.len_confAt]) $$ [Hq HrConfAt] as Hq
  · iframe Hq HrConfAt
  try wp_auto
  wp_apply wp_set_chain q ({ s with role := r.role, leaders := r.leaders, ledLog := r.ledLog, ledConf := r.ledConf, ledAt := r.ledAt, elAt := r.elAt, config := r.config, confAt := r.confAt } : State) _ _  $$ [Hq HrChain] as Hq
  · iframe Hq HrChain
  try wp_auto
  wp_apply wp_set_termLen q ({ s with role := r.role, leaders := r.leaders, ledLog := r.ledLog, ledConf := r.ledConf, ledAt := r.ledAt, elAt := r.elAt, config := r.config, confAt := r.confAt, chain := r.chain } : State) _ _  $$ [Hq HrTermLen] as Hq
  · iframe Hq HrTermLen
  try wp_auto
  generalize hns : ({ s with role := r.role, leaders := r.leaders, ledLog := r.ledLog, ledConf := r.ledConf, ledAt := r.ledAt, elAt := r.elAt, config := r.config, confAt := r.confAt, chain := r.chain, termLen := r.termLen } : State) = s10
  wp_apply wp_set_viol q s10 _ _  $$ [Hq HrViol] as Hq
  · iframe Hq HrViol
  try wp_auto
  obtain ⟨wv, hwv, Ho⟩ := bind_ok Ho
  wp_apply wp_w e ev wv $$ [He] as %uw %Huw
  · iframe He; ipureintro; exact hwv
  try wp_auto
  rw [decide_w64_eq, Huw, show sint.Z (W64 1) = 1 from rfl, decide_eq_beq']
  cases hw1 : (wv == 1)
  · rw [hw1] at Ho
    simp only [Bool.false_eq_true, ite_false, pure_ok, Except.ok.injEq] at Ho
    subst Ho hns
    try wp_auto
    imodintro
    iapply HΦ
    iunfold succOwn
    isplitr
    · ipureintro; rfl
    iexact Hq
  rw [hw1] at Ho
  simp only [ite_true] at Ho
  obtain ⟨qi, hqi, Ho⟩ := bind_ok Ho
  simp only [pure_ok, Except.ok.injEq] at Ho
  subst Ho hns
  try wp_auto
  icases queueRO_at g.Queue' s.queue n ⟨Hn, by rw [HWf.len_queue]; exact Hlt⟩ $$ HQueue with ⟨%qv, #Hqa, #Hqs⟩
  ihave %Hql := qitemsRO_len _ _ $$ Hqs
  wp_apply wp_load_at _ _ qv Hn $$ [Hqa]
  · iexact Hqa
  try wp_auto
  ihave #Hqs' := Hqs
  iunfold qitemsRO at Hqs'
  icases Hqs' with ⟨%items, #Hitems, #Hb⟩
  have hqlb : (s.queue[sint.nat n]!).length ≤ bb := by
    exact getElem!_mem' (P := fun x : List QItem => x.length ≤ bb) (fun x hx => (HW.queue x hx).1) (Nat.zero_le _)
  have hlen1 : sint.Z (qv.len + W64 1) = (s.queue[sint.nat n]!).length + 1 := by
    rw [sint_add (by rw [Hql, sint_one]; omega) (by rw [Hql, sint_one]; omega), Hql, sint_one]
  wp_apply (wp_slice_make3 (V := G.QItem) (W64 0) (qv.len + W64 1) ⟨by rw [sint_zero]; omega, by rw [sint_zero, hlen1]; omega⟩) as %o ⟨Ho, Hocap, -⟩
  try wp_auto
  wp_apply wp_slice_append o _ qv items DFrac.discard $$ [Ho Hocap Hitems] as %o1 ⟨Ho1, Hocap1, -⟩
  · iframe Ho Hocap; iexact Hitems
  try wp_auto
  wp_apply wp_queued p s n e ev qi $$ [Hs He] as %gqi #Hgqi
  · iframe Hs He; ipureintro; exact ⟨Hn, Hlt, hqi⟩
  try wp_auto
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %sl1 ⟨Hsl1, -⟩
  wp_apply wp_slice_append $$ [Ho1 Hocap1 Hsl1] as %o2 ⟨Ho2, -, -⟩
  · iframe
  try wp_auto
  imod ownSlice_persist $$ Ho2 with #Ho2
  ihave #Hnq : qitemsRO o2 (s.queue[sint.nat n]! ++ [qi]) $$ [Ho2 Hb Hgqi]
  · iunfold qitemsRO
    iexists _
    rw [List.replicate_zero, List.nil_append]
    iframe Ho2
    iapply (BigSepL2.bigSepL2_snoc (Φ := fun _ g x => qitemRO (GF := GF) g x)).2
    iframe Hb Hgqi
  wp_apply wp_setQueue g.Queue' s.queue n _ _ $$ [HQueue Hnq] as %out #Hout
  · iframe HQueue Hnq; ipureintro; exact ⟨Hn, by rw [HWf.len_queue]; exact Hlt⟩
  try wp_auto
  wp_apply wp_set_queue q ({ s with role := r.role, leaders := r.leaders, ledLog := r.ledLog, ledConf := r.ledConf, ledAt := r.ledAt, elAt := r.elAt, config := r.config, confAt := r.confAt, chain := r.chain, termLen := r.termLen, viol := r.viol } : State) out (s.queue.set (sint.nat n) (s.queue[sint.nat n]! ++ [qi]))
    (by rw [List.length_set, HWf.len_queue]) $$ [Hq Hout] as Hq
  · iframe Hq Hout
  try wp_auto
  imodintro
  iapply HΦ
  iunfold succOwn
  isplitr
  · ipureintro; rfl
  iexact Hq

end proof

end AntCheck
end EtcdGrove
end Perennial

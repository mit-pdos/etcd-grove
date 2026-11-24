/-
Lean-first (no Rocq counterpart). #33 S3b W5 (2026-11-23): the proof of `State.Send` (B 510-593).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State__Send
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State__clone
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Event__msg
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Event__has
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Event__cause
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Msg__from
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Msg__typ
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Msg__to
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Msg__term
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Msg__reject
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Msg__index
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.isForwarded
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Set__Has
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.setPre
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.factsHas
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.VoteFact
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.votesHas
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.factsAdd
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.IsReq
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.SnapOk
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.ReqFactIn
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State__Sendable
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.AckFact
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.msgSeqHead
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State__PrevOk
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State__HasFirst
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Max
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.setConfirmed
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State__EffTerm
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.isUnmodelled
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.StateLaws
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.EvalLaws
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Init0Laws
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.OnDiskLaws
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.BootSendProofLaws
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Within.Send

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntCheck

open Iris Iris.BI Iris.ProofMode

-- an action's `return nil, false`
set_option hygiene false in
local macro "bsp_none" : tactic =>
  `(tactic| ((try iintro -); (try wp_auto); iapply HΦ; iunfold succOwn; ipureintro; rfl))

-- an action's `return ns, true` (the successor owned as `Hq`)
set_option hygiene false in
local macro "bsp_some" : tactic =>
  `(tactic| ((try iintro -); (try wp_auto); iapply HΦ; iunfold succOwn; isplitr; (· ipureintro; rfl); iexact Hq))

section proof
set_option linter.unusedSimpArgs false
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Assumptions]

set_option maxHeartbeats 1600000 in
theorem State.Send.wp_proof
    (wp_clone : State.clone.spec (GF := GF) (hG := hG))
    (wp_msg : Event.msg.spec (GF := GF) (hG := hG))
    (wp_has : Event.has.spec (GF := GF) (hG := hG))
    (wp_cause : Event.cause.spec (GF := GF) (hG := hG))
    (wp_from : Msg.from.spec (GF := GF) (hG := hG))
    (wp_typ : Msg.typ.spec (GF := GF) (hG := hG))
    (wp_to : Msg.to.spec (GF := GF) (hG := hG))
    (wp_term : Msg.term.spec (GF := GF) (hG := hG))
    (wp_reject : Msg.reject.spec (GF := GF) (hG := hG))
    (wp_index : Msg.index.spec (GF := GF) (hG := hG))
    (wp_isForwarded : isForwarded.spec (GF := GF) (hG := hG))
    (wp_SetHas : Set.Has.spec (GF := GF) (hG := hG))
    (wp_setPre : setPre.spec (GF := GF) (hG := hG))
    (wp_factsHas : factsHas.spec (GF := GF) (hG := hG))
    (wp_VoteFact : VoteFact.spec (GF := GF) (hG := hG))
    (wp_votesHas : votesHas.spec (GF := GF) (hG := hG))
    (wp_factsAdd : factsAdd.spec (GF := GF) (hG := hG))
    (wp_IsReq : IsReq.spec (GF := GF) (hG := hG))
    (wp_SnapOk : SnapOk.spec (GF := GF) (hG := hG))
    (wp_ReqFactIn : ReqFactIn.spec (GF := GF) (hG := hG))
    (wp_Sendable : State.Sendable.spec (GF := GF) (hG := hG))
    (wp_AckFact : AckFact.spec (GF := GF) (hG := hG))
    (wp_msgSeqHead : msgSeqHead.spec (GF := GF) (hG := hG))
    (wp_PrevOk : State.PrevOk.spec (GF := GF) (hG := hG))
    (wp_HasFirst : State.HasFirst.spec (GF := GF) (hG := hG))
    (wp_Max : Max.spec (GF := GF) (hG := hG))
    (wp_setConfirmed : setConfirmed.spec (GF := GF) (hG := hG))
    (wp_EffTerm : State.EffTerm.spec (GF := GF) (hG := hG))
    (wp_isUnmodelled : isUnmodelled.spec (GF := GF) (hG := hG)) :
    State.Send.spec (GF := GF) (hG := hG) := by
  intro p s n e ev o
  wp_start as ⟨#Hs, #He, %Hn, %Hlt, %HBd, %Ho⟩
  ihave #Hs' := Hs
  iunfold stateRO at Hs'
  iNamed Hs'
  iNamed Hf
  iStructNamed Hp
  obtain ⟨bb, EE, HW, HNO, HCh, hbb, hEE⟩ := HBd
  unfold numBound Event.weight at hbb
  obtain ⟨m, hm, x1, hx1, hx1f, hx1t⟩ := bootSendP_send_ok Ho
  clear Ho
  have hmN : m.NumsOk := HNO.2.2.2.2.2.2.2.2.2.2.2.1 m (need_ok hm)
  iunfold configRO at HCfg
  icases HCfg with ⟨%gc, #Hgc, #Hsrv, #-, %-⟩
  iStructNamed Hgc
  ihave #Hme := strsRO_at gc.Server' s.cfg.server n ⟨Hn, Hlt⟩ $$ Hsrv
  icases undoRO_at g.Undo' s.undo n ⟨Hn, by rw [HWf.len_undo]; exact Hlt⟩ $$ HUndo with ⟨%u, #Hua, #Hu⟩
  wp_auto
  wp_apply wp_msg e ev m $$ [He] as %gm #Hm
  · iframe He; ipureintro; exact hm
  try wp_auto
  wp_apply wp_load_at _ _ _ Hn $$ [Hme] as -
  · iexact Hme
  try wp_auto
  rw [show (github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.FCause : val) = #fCause from rfl]
  wp_apply wp_has e ev fCause ev.cause.isSome $$ [He]
  · iframe He; ipureintro; exact Event.hasF_Cause _
  try wp_auto
  rw [show (github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.FB : val) = #fB from rfl]
  wp_apply wp_has e ev fB ev.b $$ [He]
  · iframe He; ipureintro; exact Event.hasF_B _
  try wp_auto
  -- `mine`, `cast`: the write's facts and votes, for a boot report
  wp_join iprop(∃ (msl csl : GoSlice), mine_ptr ↦ msl ∗ cast_ptr ↦ csl ∗ s_ptr ↦ p ∗ n_ptr ↦ n ∗
      factsRO msl (bootSendP_mine ev.b (s.undo[sint.nat n]!)) ∗ votesRO csl (bootSendP_cast ev.b (s.undo[sint.nat n]!)))
    at next with [mine cast s n] as ⟨%msl, %csl, mine, cast, s, n, #Hmine, #Hcast⟩
  · ihave #Hnf := Init0_factsNil (GF := GF)
    ihave #Hnv := Init0_votesNil (GF := GF)
    cases hb : ev.b
    · try wp_auto
      wp_join_done
      iexists _, _
      iframe mine cast s n
      unfold bootSendP_mine bootSendP_cast
      iframe Hnf Hnv
    try wp_auto
    wp_apply wp_load_at _ _ u Hn $$ [Hua]
    · iexact Hua
    cases hu : s.undo[sint.nat n]! with
    | none =>
      iunfold preRO at Hu
      icases Hu with %Hnull
      subst Hnull
      try wp_auto
      wp_join_done
      iexists _, _
      iframe mine cast s n
      unfold bootSendP_mine bootSendP_cast
      iframe Hnf Hnv
    | some pu =>
      iunfold preRO at Hu
      icases Hu with ⟨%gp, #Hgp, %Hpf, #Hsuf, #Hms, #Hvs, #-⟩
      ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hgp
      iStructNamed Hgp
      wp_if_destruct
      · exact absurd rfl Hnn
      try wp_auto
      wp_apply wp_load_at _ _ u Hn $$ [Hua]
      · iexact Hua
      try wp_auto
      wp_apply wp_load_at _ _ u Hn $$ [Hua]
      · iexact Hua
      try wp_auto
      wp_join_done
      iexists _, _
      iframe mine cast s n
      unfold bootSendP_mine bootSendP_cast
      iframe Hms Hvs
  -- `dur := s.Undo[n] == nil || s.Undo[n].Made`
  wp_join (Q := fun v => iprop(⌜v = #(bootSendP_dur (s.undo[sint.nat n]!))⌝ ∗ s_ptr ↦ p ∗ n_ptr ↦ n))
    at (if: _ then #true else _) with [s n] as ⟨%Hv, s, n⟩
  · wp_apply wp_load_at _ _ u Hn $$ [Hua]
    · iexact Hua
    cases hu : s.undo[sint.nat n]! with
    | none =>
      iunfold preRO at Hu
      icases Hu with %Hnull
      subst Hnull
      try wp_auto
      iframe s n; ipureintro; rfl
    | some pu =>
      iunfold preRO at Hu
      icases Hu with ⟨%gp, #Hgp, %Hpf, #-, #-, #-, #-⟩
      ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hgp
      iStructNamed Hgp
      wp_if_destruct
      · exact absurd rfl Hnn
      try wp_auto
      wp_apply wp_load_at _ _ u Hn $$ [Hua]
      · iexact Hua
      try wp_auto
      iframe s n; ipureintro; unfold bootSendP_dur; rw [Hpf.2.2.2.2.2.2.2]
  subst Hv
  try wp_auto
  -- `m.from() == me || isForwarded(m.typ())`
  wp_join (Q := fun v => iprop(⌜v = #x1⌝ ∗ m_ptr ↦ gm ∗ me_ptr ↦ s.cfg.server[sint.nat n]!))
    at (if: _ then #true else _) with [m me] as ⟨%Hv, m, me⟩
  · obtain ⟨y, hy, hyt, hyf⟩ := orM_ok hx1
    obtain ⟨fr, hfr, hy⟩ := bind_ok hy
    simp only [pure_ok, Except.ok.injEq] at hy
    subst hy
    rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Msg.TypeAssumptions.ptr_unfold'from.method_unfold]
    try wp_auto
    wp_apply wp_from gm m fr $$ [Hm]
    · iframe Hm; ipureintro; exact hfr
    try wp_auto
    by_cases hfm : fr = s.cfg.server[sint.nat n]!
    · rw [decide_eq_true hfm]
      have := hyt (by simpa using hfm)
      subst this
      try wp_auto
      iframe m me; ipureintro; rfl
    rw [decide_eq_false hfm]
    have hz := hyf (by simpa using hfm)
    obtain ⟨ty, hty, hz⟩ := bind_ok hz
    simp only [pure_ok, Except.ok.injEq] at hz
    subst hz
    try wp_auto
    rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Msg.TypeAssumptions.ptr_unfold'typ.method_unfold]
    try wp_auto
    wp_apply wp_typ gm m ty $$ [Hm]
    · iframe Hm; ipureintro; exact hty
    try wp_auto
    wp_apply wp_isForwarded ty
    try wp_auto
    iframe m me; ipureintro; rfl
  subst Hv
  cases x1
  · have := hx1f rfl
    subst this
    try wp_auto
    iapply HΦ; iunfold succOwn; ipureintro; rfl
  obtain ⟨x2, hx2, hx2f, hx2t⟩ := hx1t rfl
  try wp_auto
  -- `s.Cfg.Server.Has(m.to()) && m.to() != me`
  wp_join (Q := fun v => iprop(⌜v = #x2⌝ ∗ m_ptr ↦ gm ∗ me_ptr ↦ s.cfg.server[sint.nat n]! ∗ s_ptr ↦ p))
    at (if: _ then _ else #false) with [m me s] as ⟨%Hv, m, me, s⟩
  · obtain ⟨y, hy, hyt, hyf⟩ := andM_ok hx2
    obtain ⟨dt, hdt, hy⟩ := bind_ok hy
    simp only [pure_ok, Except.ok.injEq] at hy
    subst hy
    try wp_auto
    rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Msg.TypeAssumptions.ptr_unfold'to.method_unfold]
    try wp_auto
    wp_apply wp_to gm m dt $$ [Hm]
    · iframe Hm; ipureintro; exact hdt
    try wp_auto
    rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Set''.TypeAssumptions.ptr_unfold'Has.method_unfold]
    try wp_auto
    wp_apply wp_SetHas gc.Server' s.cfg.server dt $$ [Hsrv]
    · iexact Hsrv
    cases hhas : s.cfg.server.has dt
    · have := hyf hhas
      subst this
      try wp_auto
      iframe m me s; ipureintro; rfl
    have hz := hyt hhas
    obtain ⟨dt2, hdt2, hz⟩ := bind_ok hz
    simp only [pure_ok, Except.ok.injEq] at hz
    subst hz
    try wp_auto
    rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Msg.TypeAssumptions.ptr_unfold'to.method_unfold]
    try wp_auto
    wp_apply wp_to gm m dt2 $$ [Hm]
    · iframe Hm; ipureintro; exact hdt2
    try wp_auto
    iframe m me s; ipureintro
    by_cases hd : dt2 = s.cfg.server[sint.nat n]!
    · rw [decide_eq_true hd, show (dt2 != s.cfg.server[sint.nat n]!) = false by simpa using hd]; rfl
    · rw [decide_eq_false hd, show (dt2 != s.cfg.server[sint.nat n]!) = true by simpa using hd]; rfl
  subst Hv
  cases x2
  · have := hx2f rfl
    subst this
    try wp_auto
    iapply HΦ; iunfold succOwn; ipureintro; rfl
  have Ht := hx2t rfl
  try wp_auto
  wp_apply wp_clone p s $$ [Hs] as %q Hq
  · iexact Hs
  try wp_auto
  -- `if !(late || bt) { ns.Undo = setPre(s.Undo, n, nil) }`
  wp_join iprop(stateOwn q (if !(ev.cause.isSome || ev.b) then { s with undo := s.undo.set (sint.nat n) none } else s) ∗
      late_ptr ↦ ev.cause.isSome ∗ bt_ptr ↦ ev.b ∗ s_ptr ↦ p ∗ n_ptr ↦ n ∗ ns_ptr ↦ q)
    at next with [Hq late bt s n ns] as ⟨Hq, late, bt, s, n, ns⟩
  · by_cases hlb : (!(ev.cause.isSome || ev.b)) = true
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hlb)]
      have hl : ev.cause.isSome = false := by revert hlb; cases ev.cause.isSome <;> simp
      have hb : ev.b = false := by revert hlb; cases ev.b <;> simp
      rw [hl, hb]
      try wp_auto
      wp_apply wp_setPre g.Undo' s.undo n null none $$ [HUndo] as %uo #Huo
      · iframe HUndo; iunfold preRO; ipureintro; exact ⟨rfl, Hn, by rw [HWf.len_undo]; exact Hlt⟩
      try wp_auto
      wp_apply wp_set_undo q s uo (s.undo.set (sint.nat n) none) (by rw [List.length_set, HWf.len_undo]) $$ [Hq Huo] as Hq
      · iframe Hq Huo
      try wp_auto
      wp_join_done
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hlb)]
      have : (ev.cause.isSome || ev.b) = true := by revert hlb; cases (ev.cause.isSome || ev.b) <;> simp
      cases hl : ev.cause.isSome <;> cases hb : ev.b <;> rw [hl, hb] at this <;> simp at this <;> try wp_auto
      all_goals wp_join_done
  have hNSm : (if !(ev.cause.isSome || ev.b) then { s with undo := s.undo.set (sint.nat n) none } else s).msgs = s.msgs := by
    split <;> rfl
  have hNSc : (if !(ev.cause.isSome || ev.b) then { s with undo := s.undo.set (sint.nat n) none } else s).cfg = s.cfg := by
    split <;> rfl
  have hNSf : (if !(ev.cause.isSome || ev.b) then { s with undo := s.undo.set (sint.nat n) none } else s).confirmed = s.confirmed := by
    split <;> rfl
  generalize (if !(ev.cause.isSome || ev.b) then { s with undo := s.undo.set (sint.nat n) none } else s) = NS at Ht hNSm hNSc hNSf ⊢
  unfold bootSendP_sendTail at Ht
  obtain ⟨t, htyp, Ht⟩ := bind_ok Ht
  try wp_auto
  rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Msg.TypeAssumptions.ptr_unfold'typ.method_unfold]
  try wp_auto
  wp_apply wp_typ gm m t $$ [Hm]
  · iframe Hm; ipureintro; exact htyp
  try wp_auto
  icases intsRO_at g.CurrentTerm' s.currentTerm n ⟨Hn, by rw [HWf.len_currentTerm]; exact Hlt⟩ $$ HCurrentTerm with ⟨%ct, #Hcta, %Hct⟩
  -- `vote`
  by_cases htv : t = go!"vote"
  · rw [ite_eq_left_of_eq_true _ _ (eq_true (beq_iff_eq.mpr htv))] at Ht
    subst htv
    try wp_auto
    cases hb : ev.b
    · -- not a boot report: `m.term() == s.CurrentTerm[n] && factsHas(s.Msgs, VoteFact(m))`
      rw [hb] at Ht
      rw [ite_eq_right_of_eq_false _ _ (eq_false (by decide))] at Ht
      obtain ⟨c, hc, Ht⟩ := bind_ok Ht
      obtain ⟨x, hx, hxt, hxf⟩ := andM_ok hc
      obtain ⟨mt, hmt, hx⟩ := bind_ok hx
      simp only [pure_ok, Except.ok.injEq] at hx
      subst hx
      try wp_auto
      rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Msg.TypeAssumptions.ptr_unfold'term.method_unfold]
      try wp_auto
      wp_apply wp_term gm m mt $$ [Hm] as %ut %Hut
      · iframe Hm; ipureintro; exact hmt
      try wp_auto
      wp_apply wp_load_at _ _ ct Hn $$ [Hcta]
      · iexact Hcta
      try wp_auto
      by_cases hmt' : mt = s.currentTerm[sint.nat n]!
      · rw [decide_eq_true (bootSendP_w64_eq.2 (by rw [Hut, Hct]; exact hmt'))]
        have hc2 := hxt (by simpa using hmt')
        obtain ⟨vf, hvf, hc2⟩ := bind_ok hc2
        simp only [pure_ok, Except.ok.injEq] at hc2
        subst hc2
        try wp_auto
        wp_apply wp_VoteFact gm m vf $$ [Hm] as %gvf %Hgvf
        · iframe Hm; ipureintro; exact hvf
        try wp_auto
        wp_apply wp_factsHas g.Msgs' s.msgs gvf vf $$ [HMsgs]
        · iframe HMsgs; ipureintro; exact Hgvf
        cases hcon : s.msgs.contains vf
        all_goals rw [hcon] at Ht
        · rw [ite_eq_left_of_eq_true _ _ (eq_true (by decide))] at Ht
          cases Ht
          bsp_none
        · rw [ite_eq_right_of_eq_false _ _ (eq_false (by decide))] at Ht
          cases Ht
          bsp_some
      · rw [decide_eq_false (fun h => hmt' (by rw [← Hut, ← Hct]; exact bootSendP_w64_eq.1 h))]
        have := hxf (by simpa using hmt')
        subst this
        rw [ite_eq_left_of_eq_true _ _ (eq_true (by decide))] at Ht
        cases Ht
        bsp_none
    · -- a boot report: `dur && (factsHas(s.Msgs, VoteFact(m)) || factsHas(mine, VoteFact(m)))`
      rw [hb] at Ht
      rw [ite_eq_left_of_eq_true _ _ (eq_true (by decide))] at Ht
      obtain ⟨c, hc, Ht⟩ := bind_ok Ht
      obtain ⟨x, hx, hxt, hxf⟩ := andM_ok hc
      simp only [pure_ok, Except.ok.injEq] at hx
      subst hx
      try wp_auto
      cases hd : bootSendP_dur (s.undo[sint.nat n]!)
      · have := hxf hd
        subst this
        rw [ite_eq_left_of_eq_true _ _ (eq_true (by decide))] at Ht
        cases Ht
        bsp_none
      have hc2 := hxt hd
      obtain ⟨y, hy, hyt, hyf⟩ := orM_ok hc2
      obtain ⟨vf, hvf, hy⟩ := bind_ok hy
      simp only [pure_ok, Except.ok.injEq] at hy
      subst hy
      try wp_auto
      wp_apply wp_VoteFact gm m vf $$ [Hm] as %gvf %Hgvf
      · iframe Hm; ipureintro; exact hvf
      try wp_auto
      wp_apply wp_factsHas g.Msgs' s.msgs gvf vf $$ [HMsgs]
      · iframe HMsgs; ipureintro; exact Hgvf
      cases hcon : s.msgs.contains vf
      · have hz := hyf hcon
        obtain ⟨vf2, hvf2, hz⟩ := bind_ok hz
        simp only [pure_ok, Except.ok.injEq] at hz
        subst hz
        try wp_auto
        wp_apply wp_VoteFact gm m vf2 $$ [Hm] as %gvf2 %Hgvf2
        · iframe Hm; ipureintro; exact hvf2
        try wp_auto
        wp_apply wp_factsHas msl _ gvf2 vf2 $$ [Hmine]
        · iframe Hmine; ipureintro; exact Hgvf2
        cases hcon2 : (bootSendP_mine true (s.undo[sint.nat n]!)).contains vf2
        all_goals rw [hcon2] at Ht
        · rw [ite_eq_left_of_eq_true _ _ (eq_true (by decide))] at Ht
          cases Ht
          bsp_none
        · rw [ite_eq_right_of_eq_false _ _ (eq_false (by decide))] at Ht
          cases Ht
          bsp_some
      · have := hyt hcon
        subst this
        try wp_auto
        rw [ite_eq_right_of_eq_false _ _ (eq_false (by decide))] at Ht
        cases Ht
        bsp_some
  rw [ite_eq_right_of_eq_false _ _ (eq_false (fun h => htv (beq_iff_eq.mp h)))] at Ht
  rw [decide_eq_false htv]
  try wp_auto
  -- `voteresp`
  rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Msg.TypeAssumptions.ptr_unfold'typ.method_unfold]
  try wp_auto
  wp_apply wp_typ gm m t $$ [Hm]
  · iframe Hm; ipureintro; exact htyp
  try wp_auto
  by_cases htr : t = go!"voteresp"
  · rw [ite_eq_left_of_eq_true _ _ (eq_true (beq_iff_eq.mpr htr))] at Ht
    rw [decide_eq_true htr]
    subst htr
    try wp_auto
    obtain ⟨rj, hrj, Ht⟩ := bind_ok Ht
    rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Msg.TypeAssumptions.ptr_unfold'reject.method_unfold]
    try wp_auto
    wp_apply wp_reject gm m rj $$ [Hm]
    · iframe Hm; ipureintro; exact hrj
    cases rj
    case true =>
      rw [ite_eq_right_of_eq_false _ _ (eq_false (by decide))] at Ht
      cases Ht
      bsp_some
    rw [ite_eq_left_of_eq_true _ _ (eq_true (by decide))] at Ht
    obtain ⟨mt, hmt, Ht⟩ := bind_ok Ht
    obtain ⟨dt, hdt, Ht⟩ := bind_ok Ht
    try wp_auto
    rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Msg.TypeAssumptions.ptr_unfold'term.method_unfold]
    try wp_auto
    wp_apply wp_term gm m mt $$ [Hm] as %ut %Hut
    · iframe Hm; ipureintro; exact hmt
    try wp_auto
    rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Msg.TypeAssumptions.ptr_unfold'to.method_unfold]
    try wp_auto
    wp_apply wp_to gm m dt $$ [Hm]
    · iframe Hm; ipureintro; exact hdt
    try wp_auto
    dsimp only at Ht
    wp_join (Q := fun v => iprop(⌜v = #(s.votes.contains ({ voter := s.cfg.server[sint.nat n]!, term := mt, cand := dt } : VoteRec) ||
        (bootSendP_cast ev.b (s.undo[sint.nat n]!)).contains ({ voter := s.cfg.server[sint.nat n]!, term := mt, cand := dt } : VoteRec))⌝ ∗
        s_ptr ↦ p ∗ cast_ptr ↦ csl ∗ v_ptr ↦ ({ Voter' := s.cfg.server[sint.nat n]!, Term' := ut, Cand' := dt } : G.VoteRec)))
      at (if: _ then #true else _) with [s cast v] as ⟨%Hv, s, cast, v⟩
    · wp_apply wp_votesHas g.Votes' s.votes _ { voter := s.cfg.server[sint.nat n]!, term := mt, cand := dt } $$ [HVotes]
      · iframe HVotes; ipureintro; exact ⟨rfl, Hut, rfl⟩
      cases hv1 : s.votes.contains { voter := s.cfg.server[sint.nat n]!, term := mt, cand := dt }
      · try wp_auto
        wp_apply wp_votesHas csl _ _ { voter := s.cfg.server[sint.nat n]!, term := mt, cand := dt } $$ [Hcast]
        · iframe Hcast; ipureintro; exact ⟨rfl, Hut, rfl⟩
        iintro -
        iframe s cast v; ipureintro; rfl
      · try wp_auto
        iframe s cast v; ipureintro; rfl
    subst Hv
    cases hv : (s.votes.contains ({ voter := s.cfg.server[sint.nat n]!, term := mt, cand := dt } : VoteRec) ||
        (bootSendP_cast ev.b (s.undo[sint.nat n]!)).contains ({ voter := s.cfg.server[sint.nat n]!, term := mt, cand := dt } : VoteRec))
    · rw [hv] at Ht
      rw [ite_eq_left_of_eq_true _ _ (eq_true (by decide))] at Ht
      cases Ht
      bsp_none
    rw [hv] at Ht
    rw [ite_eq_right_of_eq_false _ _ (eq_false (by decide))] at Ht
    try wp_auto
    -- `bt && !dur`
    cases hbd : (ev.b && !bootSendP_dur (s.undo[sint.nat n]!))
    · rw [hbd] at Ht
      rw [ite_eq_right_of_eq_false _ _ (eq_false (by decide))] at Ht
      obtain ⟨dt2, hdt2, Ht⟩ := bind_ok Ht
      obtain ⟨mt2, hmt2, Ht⟩ := bind_ok Ht
      rw [hdt] at hdt2; cases hdt2
      rw [hmt] at hmt2; cases hmt2
      cases Ht
      have hbd' : (ev.b && !bootSendP_dur (s.undo[sint.nat n]!)) = false := hbd
      revert hbd'
      cases ev.b <;> cases bootSendP_dur (s.undo[sint.nat n]!) <;> intro hbd' <;> simp at hbd' <;> try wp_auto
      all_goals
        rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Msg.TypeAssumptions.ptr_unfold'to.method_unfold]
        try wp_auto
        wp_apply wp_to gm m dt $$ [Hm]
        · iframe Hm; ipureintro; exact hdt
        try wp_auto
        rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Msg.TypeAssumptions.ptr_unfold'term.method_unfold]
        try wp_auto
        wp_apply wp_term gm m mt $$ [Hm] as %ut2 %Hut2
        · iframe Hm; ipureintro; exact hmt
        try wp_auto
        wp_apply wp_factsAdd g.Msgs' s.msgs _ { type := go!"grant", src := s.cfg.server[sint.nat n]!, dst := dt, term := mt } $$ [HMsgs] as %fo #Hfo
        · iframe HMsgs; ipureintro
          refine ⟨⟨rfl, rfl, rfl, Hut2, rfl, rfl, rfl⟩, ?_⟩
          have := HW.msgs_len; omega
        try wp_auto
        wp_apply wp_set_msgs q NS fo _ $$ [Hq Hfo] as Hq
        · iframe Hq Hfo
        try wp_auto
        bsp_some
    rw [hbd] at Ht
    rw [ite_eq_left_of_eq_true _ _ (eq_true (by decide))] at Ht
    cases Ht
    have hbd' : (ev.b && !bootSendP_dur (s.undo[sint.nat n]!)) = true := hbd
    revert hbd'
    cases ev.b <;> cases bootSendP_dur (s.undo[sint.nat n]!) <;> intro hbd' <;> simp at hbd'
    bsp_none
  rw [ite_eq_right_of_eq_false _ _ (eq_false (fun h => htr (beq_iff_eq.mp h)))] at Ht
  rw [decide_eq_false htr]
  try wp_auto
  have hms : m.size ≤ ev.size := by unfold Event.size; rw [need_ok hm]; simp; omega
  ihave #Hrla := strsRO_at g.Role' s.role n ⟨Hn, by rw [HWf.len_role]; exact Hlt⟩ $$ HRole
  -- `IsReq(m)`
  obtain ⟨rq, hrq, Ht⟩ := bind_ok Ht
  wp_apply wp_IsReq gm m rq $$ [Hm]
  · iframe Hm; ipureintro; exact hrq
  cases rq
  case true =>
    rw [ite_eq_left_of_eq_true _ _ (eq_true (by decide))] at Ht
    obtain ⟨x, hx, Ht⟩ := bind_ok Ht
    try wp_auto
    -- `bt || (m.term() == s.CurrentTerm[n] && s.Role[n] == Leader)`
    wp_join (Q := fun v => iprop(⌜v = #x⌝ ∗ bt_ptr ↦ ev.b ∗ s_ptr ↦ p ∗ n_ptr ↦ n ∗ m_ptr ↦ gm))
      at (if: _ then #true else _) with [bt s n m] as ⟨%Hv, bt, s, n, m⟩
    · obtain ⟨y, hy, hyt, hyf⟩ := orM_ok hx
      simp only [pure_ok, Except.ok.injEq] at hy
      subst hy
      cases hb : ev.b
      case true =>
        have := hyt hb; subst this
        try wp_auto
        iframe bt s n m; ipureintro; rfl
      have hz := hyf hb
      obtain ⟨z, hz1, hzt, hzf⟩ := andM_ok hz
      obtain ⟨mt, hmt, hz1⟩ := bind_ok hz1
      simp only [pure_ok, Except.ok.injEq] at hz1
      subst hz1
      try wp_auto
      rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Msg.TypeAssumptions.ptr_unfold'term.method_unfold]
      try wp_auto
      wp_apply wp_term gm m mt $$ [Hm] as %ut %Hut
      · iframe Hm; ipureintro; exact hmt
      try wp_auto
      wp_apply wp_load_at _ _ ct Hn $$ [Hcta]
      · iexact Hcta
      try wp_auto
      by_cases hmt' : mt = s.currentTerm[sint.nat n]!
      · rw [decide_eq_true (bootSendP_w64_eq.2 (by rw [Hut, Hct]; exact hmt'))]
        have hz2 := hzt (by simpa using hmt')
        simp only [pure_ok, Except.ok.injEq] at hz2
        subst hz2
        try wp_auto
        wp_apply wp_load_at _ _ _ Hn $$ [Hrla] as -
        · iexact Hrla
        try wp_auto
        try rw [show (github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Leader : val) = #leader from rfl]
        try wp_auto
        iframe bt s n m; ipureintro
        by_cases hrl0 : s.role[sint.nat n]! = go!"leader"
        · have hrl : s.role[sint.nat n]! = leader := hrl0
          rw [decide_eq_true hrl0, beq_of_eq' hrl]
        · have hrl : ¬ s.role[sint.nat n]! = leader := hrl0
          rw [decide_eq_false hrl0, beq_of_ne' hrl]
      · rw [decide_eq_false (fun h => hmt' (by rw [← Hut, ← Hct]; exact bootSendP_w64_eq.1 h))]
        have := hzf (by simpa using hmt')
        subst this
        try wp_auto
        iframe bt s n m; ipureintro; rfl
    subst Hv
    cases x
    · rw [ite_eq_left_of_eq_true _ _ (eq_true (by decide))] at Ht
      cases Ht
      bsp_none
    rw [ite_eq_right_of_eq_false _ _ (eq_false (by decide))] at Ht
    try wp_auto
    -- `SnapOk(s.LedLog, m) && s.Sendable(ReqFactIn(s.LedLog, m))`
    obtain ⟨c2, hc2, Ht⟩ := bind_ok Ht
    obtain ⟨so, hso, ht2, hf2⟩ := andM_ok hc2
    wp_apply wp_SnapOk g.LedLog' s.ledLog gm m so $$ [HLedLog Hm]
    · iframe HLedLog Hm; ipureintro; exact hso
    cases so
    · rw [hf2 rfl] at Ht
      rw [ite_eq_left_of_eq_true _ _ (eq_true (by decide))] at Ht
      cases Ht
      bsp_none
    have hc3 := ht2 rfl
    obtain ⟨f, hf, hc3⟩ := bind_ok hc3
    have hfw := reqFactIn_within (b := bb + ev.size) (E := EE) ⟨hmN, by omega⟩
      (fun p hp => ⟨(HW.2.2.2.2.2.2.2.2.2.2.2.2.1 p hp).1, logWithin.mono (by omega) (Nat.le_refl _) (HW.2.2.2.2.2.2.2.2.2.2.2.2.1 p hp).2⟩) hf
    unfold numOk numBound at hfw
    try wp_auto
    wp_apply wp_ReqFactIn g.LedLog' s.ledLog gm m f $$ [HLedLog Hm] as %gf #Hgf
    · iframe HLedLog Hm; ipureintro; exact hf
    try wp_auto
    wp_apply wp_Sendable p s gf f c2 $$ [Hs Hgf]
    · iframe Hs Hgf; ipureintro; exact ⟨hc3, by unfold bigOk; omega, by omega⟩
    cases c2
    · rw [ite_eq_left_of_eq_true _ _ (eq_true (by decide))] at Ht
      cases Ht
      bsp_none
    rw [ite_eq_right_of_eq_false _ _ (eq_false (by decide))] at Ht
    cases Ht
    bsp_some
  rw [ite_eq_right_of_eq_false _ _ (eq_false (by decide))] at Ht
  try wp_auto
  -- `appresp`
  try rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Msg.TypeAssumptions.ptr_unfold'typ.method_unfold]
  try wp_auto
  wp_apply wp_typ gm m t $$ [Hm]
  · iframe Hm; ipureintro; exact htyp
  try wp_auto
  by_cases hta : t = go!"appresp"
  case neg =>
    rw [ite_eq_right_of_eq_false _ _ (eq_false (fun h => hta (beq_iff_eq.mp h)))] at Ht
    rw [decide_eq_false hta]
    try wp_auto
    -- `hbresp`
    try rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Msg.TypeAssumptions.ptr_unfold'typ.method_unfold]
    try wp_auto
    wp_apply wp_typ gm m t $$ [Hm]
    · iframe Hm; ipureintro; exact htyp
    try wp_auto
    by_cases hth : t = go!"hbresp"
    · rw [ite_eq_left_of_eq_true _ _ (eq_true (beq_iff_eq.mpr hth))] at Ht
      rw [decide_eq_true hth]
      try wp_auto
      dsimp only at Ht
      wp_apply wp_load_at _ _ ct Hn $$ [Hcta]
      · iexact Hcta
      try wp_auto
      cases hb : ev.b
      · rw [hb] at Ht
        simp only [Bool.false_eq_true, ite_false] at Ht
        try wp_auto
        obtain ⟨mt, hmt, Ht⟩ := bind_ok Ht
        try wp_auto
        try rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Msg.TypeAssumptions.ptr_unfold'term.method_unfold]
        try wp_auto
        wp_apply wp_term gm m mt $$ [Hm] as %ut %Hut
        · iframe Hm; ipureintro; exact hmt
        try wp_auto
        rw [Hct, Hut]
        by_cases hle : (if ev.b then s.effTerm (sint.nat n) else s.currentTerm[sint.nat n]!) ≤ mt
        · rw [hb] at hle
          simp only [Bool.false_eq_true, ite_false, ite_true] at hle
          rw [decide_eq_true hle]
          rw [ite_eq_right_of_eq_false _ _ (eq_false (by rw [decide_eq_true hle]; decide))] at Ht
          cases Ht
          bsp_some
        · rw [hb] at hle
          simp only [Bool.false_eq_true, ite_false, ite_true] at hle
          rw [decide_eq_false hle]
          rw [ite_eq_left_of_eq_true _ _ (eq_true (by rw [decide_eq_false hle]; decide))] at Ht
          cases Ht
          bsp_none
      rw [hb] at Ht
      simp only [ite_true] at Ht
      try wp_auto
      wp_apply wp_EffTerm p s n $$ [Hs] as %ue %Hue
      · iframe Hs; ipureintro; exact ⟨Hn, Hlt⟩
      try wp_auto
      obtain ⟨mt, hmt, Ht⟩ := bind_ok Ht
      try wp_auto
      try rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Msg.TypeAssumptions.ptr_unfold'term.method_unfold]
      try wp_auto
      wp_apply wp_term gm m mt $$ [Hm] as %ut %Hut
      · iframe Hm; ipureintro; exact hmt
      try wp_auto
      rw [Hue, Hut]
      by_cases hle : (if ev.b then s.effTerm (sint.nat n) else s.currentTerm[sint.nat n]!) ≤ mt
      · rw [hb] at hle
        simp only [Bool.false_eq_true, ite_false, ite_true] at hle
        rw [decide_eq_true hle]
        rw [ite_eq_right_of_eq_false _ _ (eq_false (by rw [decide_eq_true hle]; decide))] at Ht
        cases Ht
        bsp_some
      · rw [hb] at hle
        simp only [Bool.false_eq_true, ite_false, ite_true] at hle
        rw [decide_eq_false hle]
        rw [ite_eq_left_of_eq_true _ _ (eq_true (by rw [decide_eq_false hle]; decide))] at Ht
        cases Ht
        bsp_none
    rw [ite_eq_right_of_eq_false _ _ (eq_false (fun h => hth (beq_iff_eq.mp h)))] at Ht
    rw [decide_eq_false hth]
    try wp_auto
    -- `isUnmodelled(m.typ())`
    try rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Msg.TypeAssumptions.ptr_unfold'typ.method_unfold]
    try wp_auto
    wp_apply wp_typ gm m t $$ [Hm]
    · iframe Hm; ipureintro; exact htyp
    try wp_auto
    wp_apply wp_isUnmodelled t
    cases hun : isUnmodelled t
    all_goals rw [hun] at Ht
    · rw [ite_eq_right_of_eq_false _ _ (eq_false (by decide))] at Ht
      cases Ht
      bsp_none
    · rw [ite_eq_left_of_eq_true _ _ (eq_true (by decide))] at Ht
      cases Ht
      bsp_some
  rw [ite_eq_left_of_eq_true _ _ (eq_true (beq_iff_eq.mpr hta))] at Ht
  rw [decide_eq_true hta]
  try wp_auto
  obtain ⟨rj, hrj, Ht⟩ := bind_ok Ht
  try rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Msg.TypeAssumptions.ptr_unfold'reject.method_unfold]
  try wp_auto
  wp_apply wp_reject gm m rj $$ [Hm]
  · iframe Hm; ipureintro; exact hrj
  cases rj
  case true =>
    rw [ite_eq_left_of_eq_true _ _ (eq_true (by decide))] at Ht
    cases Ht
    bsp_some
  rw [ite_eq_right_of_eq_false _ _ (eq_false (by decide))] at Ht
  try wp_auto
  cases hb : ev.b
  case true =>
    -- a boot report: the ack recorded in the write
    rw [hb] at Ht
    rw [ite_eq_left_of_eq_true _ _ (eq_true (by decide))] at Ht
    obtain ⟨mi, hmi, Ht⟩ := bind_ok Ht
    try wp_auto
    try rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Msg.TypeAssumptions.ptr_unfold'index.method_unfold]
    try wp_auto
    wp_apply wp_index gm m mi $$ [Hm] as %ui %Hui
    · iframe Hm; ipureintro; exact hmi
    try wp_auto
    by_cases hmi0 : mi = 0
    · rw [decide_eq_true ((bootSendP_w64_eq_zero).2 (by rw [Hui]; exact hmi0))]
      rw [ite_eq_left_of_eq_true _ _ (eq_true (by simp [hmi0]))] at Ht
      cases Ht
      bsp_some
    rw [decide_eq_false (fun h => hmi0 (by rw [← Hui]; exact (bootSendP_w64_eq_zero).1 h))]
    rw [ite_eq_right_of_eq_false _ _ (eq_false (by simp [hmi0]))] at Ht
    try wp_auto
    wp_apply wp_load_at _ _ u Hn $$ [Hua]
    · iexact Hua
    cases hu : s.undo[sint.nat n]! with
    | none =>
      rw [hu] at Ht
      dsimp only at Ht
      obtain ⟨ok, hok, Ht⟩ := bind_ok Ht
      cases hok
      iunfold preRO at Hu
      icases Hu with %Hnull
      subst Hnull
      rw [ite_eq_left_of_eq_true _ _ (eq_true (by decide))] at Ht
      cases Ht
      bsp_none
    | some pu =>
      rw [hu] at Ht
      dsimp only at Ht
      obtain ⟨ok, hok, Ht⟩ := bind_ok Ht
      iunfold preRO at Hu
      icases Hu with ⟨%gp, #Hgp, %Hpf, #-, #-, #-, #Hacks⟩
      ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hgp
      iStructNamed Hgp
      wp_if_destruct
      · exact absurd rfl Hnn
      try wp_auto
      obtain ⟨x, hx, hxt, hxf⟩ := andM_ok hok
      simp only [pure_ok, Except.ok.injEq] at hx
      subst hx
      rw [show bootSendP_dur (some pu) = pu.made from rfl]
      cases hmd : pu.made
      · have := hxf (by show pu.made = false; exact hmd)
        subst this
        rw [ite_eq_left_of_eq_true _ _ (eq_true (by decide))] at Ht
        cases Ht
        bsp_none
      have hz := hxt (by show pu.made = true; exact hmd)
      obtain ⟨dt, hdt, hz⟩ := bind_ok hz
      obtain ⟨mt, hmt, hz⟩ := bind_ok hz
      obtain ⟨mi2, hmi2, hz⟩ := bind_ok hz
      rw [hmi] at hmi2; cases hmi2
      simp only [pure_ok, Except.ok.injEq] at hz
      subst hz
      try wp_auto
      wp_apply wp_load_at _ _ u Hn $$ [Hua]
      · iexact Hua
      try wp_auto
      try rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Msg.TypeAssumptions.ptr_unfold'to.method_unfold]
      try wp_auto
      wp_apply wp_to gm m dt $$ [Hm]
      · iframe Hm; ipureintro; exact hdt
      try wp_auto
      try rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Msg.TypeAssumptions.ptr_unfold'term.method_unfold]
      try wp_auto
      wp_apply wp_term gm m mt $$ [Hm] as %ut %Hut
      · iframe Hm; ipureintro; exact hmt
      try wp_auto
      try rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Msg.TypeAssumptions.ptr_unfold'index.method_unfold]
      try wp_auto
      wp_apply wp_index gm m mi $$ [Hm] as %ui2 %Hui2
      · iframe Hm; ipureintro; exact hmi
      try wp_auto
      wp_apply wp_AckFact s.cfg.server[sint.nat n]! dt ut ui2 as %ga %Hga
      try wp_auto
      wp_apply wp_factsHas gp.Acks' pu.acks ga (ackFact s.cfg.server[sint.nat n]! dt mt mi) $$ [Hacks]
      · iframe Hacks; ipureintro; rw [← Hut, ← Hui2]; exact Hga
      cases hcon : pu.acks.contains (ackFact s.cfg.server[sint.nat n]! dt mt mi)
      all_goals rw [hcon] at Ht
      · rw [ite_eq_left_of_eq_true _ _ (eq_true (by decide))] at Ht
        cases Ht
        bsp_none
      · rw [ite_eq_right_of_eq_false _ _ (eq_false (by decide))] at Ht
        cases Ht
        bsp_some
  rw [hb] at Ht
  rw [ite_eq_right_of_eq_false _ _ (eq_false (by decide))] at Ht
  try wp_auto
  -- `c := ev.cause()` or `s.Pending[n]`
  obtain ⟨cv, hcv, Ht⟩ := bootSendP_cjoin_ok Ht
  wp_join iprop(∃ csl : GoSlice, c_ptr ↦ csl ∗ msgsRO csl cv ∗ s_ptr ↦ p ∗ n_ptr ↦ n ∗ ev_ptr ↦ e)
    at next with [c s n ev] as ⟨%ccsl, c, #Hc, s, n, ev⟩
  · cases hl : ev.cause.isSome
    · rw [hl] at hcv
      simp only [Bool.false_eq_true, ite_false, pure_ok, Except.ok.injEq] at hcv
      try wp_auto
      icases pendingRO_at g.Pending' s.pending n ⟨Hn, by rw [HWf.len_pending]; exact Hlt⟩ $$ HPending with ⟨%pv, #Hpa, #Hpv⟩
      wp_apply wp_load_at _ _ pv Hn $$ [Hpa]
      · iexact Hpa
      try wp_auto
      wp_join_done
      iexists _
      iframe c s n ev
      rw [← hcv]
      iexact Hpv
    · rw [hl] at hcv
      simp only [ite_true] at hcv
      try wp_auto
      wp_apply wp_cause e ev cv $$ [He] as %csl #Hcsl
      · iframe He; ipureintro; exact hcv
      try wp_auto
      wp_join_done
      iexists _
      iframe c s n ev Hcsl
  try wp_auto
  ihave %Hcl := msgsRO_len _ _ $$ Hc
  dsimp only at Ht
  -- `len(c) != 0 && IsReq(c[0]) && c[0].term() < s.CurrentTerm[n]`
  obtain ⟨x, hx, Ht⟩ := bind_ok Ht
  wp_join (Q := fun v => iprop(⌜v = #x⌝ ∗ c_ptr ↦ ccsl ∗ s_ptr ↦ p ∗ n_ptr ↦ n))
    at (if: _ then _ else #false) with [c s n] as ⟨%Hv, c, s, n⟩
  · obtain ⟨y, hy, hyt, hyf⟩ := andM_ok hx
    simp only [pure_ok, Except.ok.injEq] at hy
    subst hy
    try wp_auto
    by_cases hce : cv = []
    · have := hyf (by simp [hce])
      subst this
      rw [decide_eq_true (bootSendP_w64_eq_zero.2 (by rw [Hcl, hce]; rfl))]
      try wp_auto
      iframe c s n; ipureintro; rfl
    rw [decide_eq_false (fun h => hce (List.eq_nil_of_length_eq_zero (by
      have := bootSendP_w64_eq_zero.1 h; omega)))]
    have hz := hyt (by simpa using hce)
    try wp_auto
    icases bootSendP_msgsRO_head ccsl cv hce $$ Hc with ⟨%g0, #Hg0a, #Hg0⟩
    obtain ⟨r0, hr0, hrt, hrf⟩ := andM_ok hz
    wp_apply wp_load_at _ _ g0 (by decide) $$ [Hg0a]
    · iexact Hg0a
    try wp_auto
    wp_apply wp_IsReq g0 cv[0]! r0 $$ [Hg0]
    · iframe Hg0; ipureintro; exact hr0
    cases r0
    · have := hrf rfl
      subst this
      try wp_auto
      iframe c s n; ipureintro; rfl
    have hz2 := hrt rfl
    obtain ⟨t0, ht0, hz2⟩ := bind_ok hz2
    simp only [pure_ok, Except.ok.injEq] at hz2
    subst hz2
    try wp_auto
    have hc0 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z ccsl.len := by
      rw [Hcl, show sint.Z (W64 0) = 0 from rfl]
      have := List.length_pos_iff.2 hce
      omega
    rw [ite_eq_left_of_eq_true _ _ (eq_true hc0)]
    try wp_auto
    rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Msg.TypeAssumptions.ptr_unfold'term.method_unfold]
    try wp_auto
    rw [← ite_eq_left_of_eq_true (Val #(sliceIndexRef github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Msg (sint.Z (W64 0)) ccsl) : Expr) (Panic "slice index out of bounds") (eq_true hc0)]
    wp_apply wp_load_at _ _ g0 (by decide) $$ [Hg0a]
    · iexact Hg0a
    try wp_auto
    wp_apply wp_term g0 cv[0]! t0 $$ [Hg0] as %ut0 %Hut0
    · iframe Hg0; ipureintro; exact ht0
    try wp_auto
    wp_apply wp_load_at _ _ ct Hn $$ [Hcta]
    · iexact Hcta
    try wp_auto
    iframe c s n; ipureintro; rw [Hut0, Hct]
  subst Hv
  cases x
  case true =>
    -- a stale request: `m.index() == 0 && m.term() == s.CurrentTerm[n]`
    rw [ite_eq_left_of_eq_true _ _ (eq_true rfl)] at Ht
    obtain ⟨x, hx, Ht⟩ := bind_ok Ht
    obtain ⟨y, hy, hyt, hyf⟩ := andM_ok hx
    obtain ⟨mi, hmi, hy⟩ := bind_ok hy
    simp only [pure_ok, Except.ok.injEq] at hy
    subst hy
    try wp_auto
    try rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Msg.TypeAssumptions.ptr_unfold'index.method_unfold]
    try wp_auto
    wp_apply wp_index gm m mi $$ [Hm] as %ui %Hui
    · iframe Hm; ipureintro; exact hmi
    try wp_auto
    by_cases hmi0 : mi = 0
    case neg =>
      rw [decide_eq_false (fun h => hmi0 (by rw [← Hui]; exact (bootSendP_w64_eq_zero).1 h))]
      have := hyf (by simp [hmi0])
      subst this
      rw [ite_eq_left_of_eq_true _ _ (eq_true (by decide))] at Ht
      cases Ht
      bsp_none
    rw [decide_eq_true ((bootSendP_w64_eq_zero).2 (by rw [Hui]; exact hmi0))]
    have hz := hyt (by simp [hmi0])
    obtain ⟨mt, hmt, hz⟩ := bind_ok hz
    simp only [pure_ok, Except.ok.injEq] at hz
    subst hz
    try wp_auto
    try rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Msg.TypeAssumptions.ptr_unfold'term.method_unfold]
    try wp_auto
    wp_apply wp_term gm m mt $$ [Hm] as %ut %Hut
    · iframe Hm; ipureintro; exact hmt
    try wp_auto
    wp_apply wp_load_at _ _ ct Hn $$ [Hcta]
    · iexact Hcta
    try wp_auto
    by_cases hmt' : mt = s.currentTerm[sint.nat n]!
    · rw [decide_eq_true (bootSendP_w64_eq.2 (by rw [Hut, Hct]; exact hmt'))]
      rw [show (mt == s.currentTerm[sint.nat n]!) = true by simpa using hmt'] at Ht
      rw [ite_eq_right_of_eq_false _ _ (eq_false (by decide))] at Ht
      cases Ht
      bsp_some
    · rw [decide_eq_false (fun h => hmt' (by rw [← Hut, ← Hct]; exact bootSendP_w64_eq.1 h))]
      rw [show (mt == s.currentTerm[sint.nat n]!) = false by simpa using hmt'] at Ht
      rw [ite_eq_left_of_eq_true _ _ (eq_true (by decide))] at Ht
      cases Ht
      bsp_none
  rw [ite_eq_right_of_eq_false _ _ (eq_false (by decide))] at Ht
  try wp_auto
  -- `m.index() == 0`
  obtain ⟨mi, hmi, Ht⟩ := bind_ok Ht
  try rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Msg.TypeAssumptions.ptr_unfold'index.method_unfold]
  try wp_auto
  wp_apply wp_index gm m mi $$ [Hm] as %ui %Hui
  · iframe Hm; ipureintro; exact hmi
  try wp_auto
  by_cases hmi0 : mi = 0
  · rw [decide_eq_true ((bootSendP_w64_eq_zero).2 (by rw [Hui]; exact hmi0))]
    rw [ite_eq_left_of_eq_true _ _ (eq_true (by simp [hmi0]))] at Ht
    cases Ht
    bsp_some
  rw [decide_eq_false (fun h => hmi0 (by rw [← Hui]; exact (bootSendP_w64_eq_zero).1 h))]
  rw [ite_eq_right_of_eq_false _ _ (eq_false (by simp [hmi0]))] at Ht
  try wp_auto
  -- `len(c) == 0`
  by_cases hce : cv = []
  · rw [decide_eq_true (bootSendP_w64_eq_zero.2 (by rw [Hcl, hce]; rfl))]
    rw [ite_eq_left_of_eq_true _ _ (eq_true (by simp [hce]))] at Ht
    cases Ht
    bsp_none
  rw [decide_eq_false (fun h => hce (List.eq_nil_of_length_eq_zero (by
    have := bootSendP_w64_eq_zero.1 h; omega)))]
  rw [ite_eq_right_of_eq_false _ _ (eq_false (by simpa using hce))] at Ht
  try wp_auto
  -- `cm := msgSeqHead(c)`, `f := ReqFactIn(s.LedLog, cm)`
  have hcause : ∀ ms, ev.cause = some ms → ∀ c ∈ ms, c.NumsOk ∧ c.size ≤ bb + ev.weight := by
    intro ms hms c hc
    refine ⟨HNO.2.2.2.2.2.2.2.2.2.2.2.2 ms hms c hc, ?_⟩
    have h1 : c.size ≤ ((ev.cause.getD []).map Msg.size).sum := by
      rw [hms]; exact bootSend_le_sum_of_mem (List.mem_map_of_mem hc)
    unfold Event.weight Event.size; omega
  have hcv' : ∀ x ∈ cv, x.NumsOk ∧ x.size ≤ bb + ev.weight := by
    cases hl : ev.cause.isSome
    · rw [hl] at hcv
      simp only [Bool.false_eq_true, ite_false] at hcv
      exact bootSend_c_pending (ev := ev) (n := sint.nat n) HW hcv
    · rw [hl] at hcv
      simp only [ite_true] at hcv
      exact bootSend_c_cause hcause hcv
  obtain ⟨cm, hcm, Ht⟩ := bind_ok Ht
  have hcmN := bootSend_cm hcv' hcm
  wp_apply wp_msgSeqHead ccsl cv cm $$ [Hc] as %gcm #Hcm
  · iframe Hc; ipureintro; exact hcm
  try wp_auto
  obtain ⟨f, hf, Ht⟩ := bind_ok Ht
  have hfw := reqFactIn_within (b := bb + ev.weight) (E := EE) hcmN
    (fun p hp => ⟨(HW.2.2.2.2.2.2.2.2.2.2.2.2.1 p hp).1, logWithin.mono (by omega) (Nat.le_refl _) (HW.2.2.2.2.2.2.2.2.2.2.2.2.1 p hp).2⟩) hf
  have hlast := bootSend_last_bigOk hcmN HW (by unfold Event.weight; omega) hf
  unfold numOk numBound at hfw
  wp_apply wp_ReqFactIn g.LedLog' s.ledLog gcm cm f $$ [HLedLog Hcm] as %gf #Hgf
  · iframe HLedLog Hcm; ipureintro; exact hf
  try wp_auto
  ihave #Hgf' := Hgf
  iunfold appendFactRO at Hgf'
  icases Hgf' with ⟨%Hgfp, #Hgfe⟩
  ihave %Hgfl := logRO_len _ _ $$ Hgfe
  have hlastZ : sint.Z (gf.PrevLogIndex' + gf.Entries'.len) = f.prevLogIndex + f.entries.length := by
    rw [sint_add (by rw [Hgfp.2.2.2.1, Hgfl]; unfold bigOk at hlast; omega)
      (by rw [Hgfp.2.2.2.1, Hgfl]; unfold bigOk at hlast; omega), Hgfp.2.2.2.1, Hgfl]
  try dsimp only at Ht
  -- `(cm.typ() == "app" || cm.typ() == "snap") && SnapOk(s.LedLog, cm) && s.Sendable(f)`
  obtain ⟨x, hx, Ht⟩ := bind_ok Ht
  wp_join (Q := fun v => iprop(⌜v = #x⌝ ∗ cm_ptr ↦ gcm ∗ s_ptr ↦ p ∗ f_ptr ↦ gf))
    at (if: _ then _ else #false) with [cm s f] as ⟨%Hv, cm, s, f⟩
  · obtain ⟨y, hy, hyt, hyf⟩ := andM_ok hx
    wp_join (Q := fun v => iprop(⌜v = #y⌝ ∗ cm_ptr ↦ gcm))
      at (if: _ then #true else _) with [cm] as ⟨%Hv2, cm⟩
    · obtain ⟨z, hz, hzt, hzf⟩ := orM_ok hy
      obtain ⟨ct1, hct1, hz⟩ := bind_ok hz
      simp only [pure_ok, Except.ok.injEq] at hz
      subst hz
      try rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Msg.TypeAssumptions.ptr_unfold'typ.method_unfold]
      try wp_auto
      wp_apply wp_typ gcm cm ct1 $$ [Hcm]
      · iframe Hcm; ipureintro; exact hct1
      try wp_auto
      by_cases hca : ct1 = go!"app"
      · rw [decide_eq_true hca]
        have := hzt (by simpa using hca)
        subst this
        try wp_auto
        iframe cm; ipureintro; rfl
      rw [decide_eq_false hca]
      have hz2 := hzf (by simpa using hca)
      obtain ⟨ct2, hct2, hz2⟩ := bind_ok hz2
      simp only [pure_ok, Except.ok.injEq] at hz2
      subst hz2
      try wp_auto
      try rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Msg.TypeAssumptions.ptr_unfold'typ.method_unfold]
      try wp_auto
      wp_apply wp_typ gcm cm ct2 $$ [Hcm]
      · iframe Hcm; ipureintro; exact hct2
      try wp_auto
      iframe cm; ipureintro
      by_cases hcs : ct2 = go!"snap"
      · rw [decide_eq_true hcs, show (ct2 == go!"snap") = true by simpa using hcs]
      · rw [decide_eq_false hcs, show (ct2 == go!"snap") = false by simpa using hcs]
    subst Hv2
    cases y
    · have := hyf rfl
      subst this
      try wp_auto
      iframe cm s f; ipureintro; rfl
    have hz := hyt rfl
    obtain ⟨so, hso, hst, hsf⟩ := andM_ok hz
    try wp_auto
    wp_apply wp_SnapOk g.LedLog' s.ledLog gcm cm so $$ [HLedLog Hcm]
    · iframe HLedLog Hcm; ipureintro; exact hso
    cases so
    · have := hsf rfl
      subst this
      try wp_auto
      iframe cm s f; ipureintro; rfl
    have hz2 := hst rfl
    try wp_auto
    wp_apply wp_Sendable p s gf f x $$ [Hs Hgf]
    · iframe Hs Hgf; ipureintro; exact ⟨hz2, by unfold bigOk; omega, by have := hfw.2.1; unfold Event.weight at this; omega⟩
    iframe cm s f; ipureintro; rfl
  subst Hv
  cases x
  · rw [ite_eq_left_of_eq_true _ _ (eq_true (by decide))] at Ht
    cases Ht
    bsp_none
  rw [ite_eq_right_of_eq_false _ _ (eq_false (by decide))] at Ht
  try wp_auto
  -- `m.to() == cm.from() && m.term() == cm.term() && s.CurrentTerm[n] == cm.term()`
  obtain ⟨x, hx, Ht⟩ := bind_ok Ht
  wp_join (Q := fun v => iprop(⌜v = #x⌝ ∗ m_ptr ↦ gm ∗ cm_ptr ↦ gcm ∗ s_ptr ↦ p ∗ n_ptr ↦ n))
    at (if: _ then _ else #false) with [m cm s n] as ⟨%Hv, m, cm, s, n⟩
  · obtain ⟨y, hy, hyt, hyf⟩ := andM_ok hx
    obtain ⟨dt, hdt, hy⟩ := bind_ok hy
    obtain ⟨cf, hcf, hy⟩ := bind_ok hy
    simp only [pure_ok, Except.ok.injEq] at hy
    subst hy
    try rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Msg.TypeAssumptions.ptr_unfold'to.method_unfold]
    try wp_auto
    wp_apply wp_to gm m dt $$ [Hm]
    · iframe Hm; ipureintro; exact hdt
    try wp_auto
    try rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Msg.TypeAssumptions.ptr_unfold'from.method_unfold]
    try wp_auto
    wp_apply wp_from gcm cm cf $$ [Hcm]
    · iframe Hcm; ipureintro; exact hcf
    try wp_auto
    by_cases hdc : dt = cf
    case neg =>
      rw [decide_eq_false hdc]
      have := hyf (by simpa using hdc)
      subst this
      try wp_auto
      iframe m cm s n; ipureintro; rfl
    rw [decide_eq_true hdc]
    have hz := hyt (by simpa using hdc)
    obtain ⟨z, hz, hzt, hzf⟩ := andM_ok hz
    obtain ⟨mt, hmt, hz⟩ := bind_ok hz
    obtain ⟨cmt, hcmt, hz⟩ := bind_ok hz
    simp only [pure_ok, Except.ok.injEq] at hz
    subst hz
    try wp_auto
    try rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Msg.TypeAssumptions.ptr_unfold'term.method_unfold]
    try wp_auto
    wp_apply wp_term gm m mt $$ [Hm] as %ut %Hut
    · iframe Hm; ipureintro; exact hmt
    try wp_auto
    try rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Msg.TypeAssumptions.ptr_unfold'term.method_unfold]
    try wp_auto
    wp_apply wp_term gcm cm cmt $$ [Hcm] as %ucmt %Hucmt
    · iframe Hcm; ipureintro; exact hcmt
    try wp_auto
    by_cases htt : mt = cmt
    case neg =>
      rw [decide_eq_false (fun h => htt (by rw [← Hut, ← Hucmt]; exact bootSendP_w64_eq.1 h))]
      have := hzf (by simpa using htt)
      subst this
      try wp_auto
      iframe m cm s n; ipureintro; rfl
    rw [decide_eq_true (bootSendP_w64_eq.2 (by rw [Hut, Hucmt]; exact htt))]
    have hz2 := hzt (by simpa using htt)
    obtain ⟨cmt2, hcmt2, hz2⟩ := bind_ok hz2
    rw [hcmt] at hcmt2; cases hcmt2
    simp only [pure_ok, Except.ok.injEq] at hz2
    subst hz2
    try wp_auto
    wp_apply wp_load_at _ _ ct Hn $$ [Hcta]
    · iexact Hcta
    try wp_auto
    try rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Msg.TypeAssumptions.ptr_unfold'term.method_unfold]
    try wp_auto
    wp_apply wp_term gcm cm cmt $$ [Hcm] as %ucmt2 %Hucmt2
    · iframe Hcm; ipureintro; exact hcmt
    try wp_auto
    iframe m cm s n; ipureintro
    by_cases hct : s.currentTerm[sint.nat n]! = cmt
    · rw [decide_eq_true (bootSendP_w64_eq.2 (by rw [Hct, Hucmt2]; exact hct)),
        show (s.currentTerm[sint.nat n]! == cmt) = true by simpa using hct]
    · rw [decide_eq_false (fun h => hct (by rw [← Hct, ← Hucmt2]; exact bootSendP_w64_eq.1 h)),
        show (s.currentTerm[sint.nat n]! == cmt) = false by simpa using hct]
  subst Hv
  cases x
  · rw [ite_eq_left_of_eq_true _ _ (eq_true (by decide))] at Ht
    cases Ht
    bsp_none
  rw [ite_eq_right_of_eq_false _ _ (eq_false (by decide))] at Ht
  try wp_auto
  -- `m.index() == last && s.PrevOk(n, f) && s.HasFirst(n, f, len(f.Entries))`
  obtain ⟨x, hx, Ht⟩ := bind_ok Ht
  wp_join (Q := fun v => iprop(⌜v = #x⌝ ∗ m_ptr ↦ gm ∗ s_ptr ↦ p ∗ n_ptr ↦ n ∗ f_ptr ↦ gf ∗
      last_ptr ↦ (gf.PrevLogIndex' + gf.Entries'.len)))
    at (if: _ then _ else #false) with [m s n f last] as ⟨%Hv, m, s, n, f, last⟩
  · obtain ⟨y, hy, hyt, hyf⟩ := andM_ok hx
    obtain ⟨mi2, hmi2, hy⟩ := bind_ok hy
    rw [hmi] at hmi2; cases hmi2
    simp only [pure_ok, Except.ok.injEq] at hy
    subst hy
    try rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Msg.TypeAssumptions.ptr_unfold'index.method_unfold]
    try wp_auto
    wp_apply wp_index gm m mi $$ [Hm] as %ui2 %Hui2
    · iframe Hm; ipureintro; exact hmi
    try wp_auto
    by_cases hil : mi = f.prevLogIndex + f.entries.length
    case neg =>
      rw [decide_eq_false (fun h => hil (by rw [← Hui2, ← hlastZ]; exact bootSendP_w64_eq.1 h))]
      have := hyf (by simpa using hil)
      subst this
      try wp_auto
      iframe m s n f last; ipureintro; rfl
    rw [decide_eq_true (bootSendP_w64_eq.2 (by rw [Hui2, hlastZ]; exact hil))]
    have hz := hyt (by simpa using hil)
    obtain ⟨po, hpo, hpt, hpf⟩ := andM_ok hz
    try wp_auto
    wp_apply wp_PrevOk p s n gf f po $$ [Hs Hgf]
    · iframe Hs Hgf; ipureintro; exact ⟨Hn, Hlt, hpo⟩
    cases po
    · have := hpf rfl
      subst this
      try wp_auto
      iframe m s n f last; ipureintro; rfl
    have hz2 := hpt rfl
    try wp_auto
    wp_apply wp_HasFirst p s n gf f gf.Entries'.len x $$ [Hs Hgf]
    · iframe Hs Hgf; ipureintro
      refine ⟨Hn, Hlt, by rw [Hgfl]; exact hz2, hfw.1, ?_⟩
      have := hfw.2.1; unfold numOk numBound Event.weight at *; rw [Hgfl]; omega
    iframe m s n f last; ipureintro; rfl
  subst Hv
  cases x
  case true =>
    -- the ack of the whole append, and `Confirmed`
    rw [ite_eq_left_of_eq_true _ _ (eq_true rfl)] at Ht
    obtain ⟨ct', hct', Ht⟩ := bind_ok Ht
    obtain ⟨cf', hcf', Ht⟩ := bind_ok Ht
    cases Ht
    try wp_auto
    try rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Msg.TypeAssumptions.ptr_unfold'from.method_unfold]
    try wp_auto
    wp_apply wp_from gcm cm cf' $$ [Hcm]
    · iframe Hcm; ipureintro; exact hcf'
    try wp_auto
    try rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Msg.TypeAssumptions.ptr_unfold'term.method_unfold]
    try wp_auto
    wp_apply wp_term gcm cm ct' $$ [Hcm] as %ucmt3 %Hucmt3
    · iframe Hcm; ipureintro; exact hct'
    try wp_auto
    wp_apply wp_AckFact s.cfg.server[sint.nat n]! cf' ucmt3 (gf.PrevLogIndex' + gf.Entries'.len) as %ga %Hga
    rw [Hucmt3, hlastZ] at Hga
    try wp_auto
    wp_apply wp_factsAdd g.Msgs' s.msgs ga _ $$ [HMsgs] as %fo #Hfo
    · iframe HMsgs; ipureintro
      refine ⟨Hga, ?_⟩
      have := HW.msgs_len; omega
    try wp_auto
    wp_apply wp_set_msgs q NS fo _ $$ [Hq Hfo] as Hq
    · iframe Hq Hfo
    try wp_auto
    icases confirmedsRO_at g.Confirmed' s.confirmed n ⟨Hn, by rw [HWf.len_confirmed]; exact Hlt⟩ $$ HConfirmed with ⟨%gold, #Hold, %Hgold⟩
    wp_apply wp_load_at _ _ gold Hn $$ [Hold]
    · iexact Hold
    try wp_auto
    -- `idx := last`, or `Max(old.Index, last)` in the same term
    wp_join iprop(∃ w : w64, idx_ptr ↦ w ∗
        ⌜sint.Z w = (if (s.confirmed[sint.nat n]!.term == ct') = true then
          imax s.confirmed[sint.nat n]!.index (f.prevLogIndex + f.entries.length)
          else f.prevLogIndex + f.entries.length)⌝ ∗
        old_ptr ↦ gold ∗ cm_ptr ↦ gcm ∗ last_ptr ↦ (gf.PrevLogIndex' + gf.Entries'.len))
      at next with [idx old cm last] as ⟨%widx, idx, %Hwidx, old, cm, last⟩
    · try rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Msg.TypeAssumptions.ptr_unfold'term.method_unfold]
      try wp_auto
      wp_apply wp_term gcm cm ct' $$ [Hcm] as %ucmt4 %Hucmt4
      · iframe Hcm; ipureintro; exact hct'
      try wp_auto
      by_cases hot : s.confirmed[sint.nat n]!.term = ct'
      · rw [decide_eq_true (bootSendP_w64_eq.2 (by rw [Hgold.1, Hucmt4]; exact hot))]
        try wp_auto
        wp_apply wp_Max gold.Index' (gf.PrevLogIndex' + gf.Entries'.len) as %wm %Hwm
        try wp_auto
        wp_join_done
        iexists _
        iframe idx old cm last
        ipureintro
        rw [show (s.confirmed[sint.nat n]!.term == ct') = true by simpa using hot]
        rw [Hwm, Hgold.2, hlastZ]; rfl
      · rw [decide_eq_false (fun h => hot (by rw [← Hgold.1, ← Hucmt4]; exact bootSendP_w64_eq.1 h))]
        try wp_auto
        wp_join_done
        iexists _
        iframe idx old cm last
        ipureintro
        rw [show (s.confirmed[sint.nat n]!.term == ct') = false by simpa using hot]
        rw [hlastZ]; rfl
    try wp_auto
    try rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Msg.TypeAssumptions.ptr_unfold'term.method_unfold]
    try wp_auto
    wp_apply wp_term gcm cm ct' $$ [Hcm] as %ucmt5 %Hucmt5
    · iframe Hcm; ipureintro; exact hct'
    try wp_auto
    wp_apply wp_setConfirmed g.Confirmed' s.confirmed n { Term' := ucmt5, Index' := widx }
      { term := ct', index := (if (s.confirmed[sint.nat n]!.term == ct') = true then
          imax s.confirmed[sint.nat n]!.index (f.prevLogIndex + f.entries.length)
          else f.prevLogIndex + f.entries.length) } $$ [HConfirmed] as %co #Hco
    · iframe HConfirmed; ipureintro
      exact ⟨⟨Hucmt5, Hwidx⟩, Hn, by rw [HWf.len_confirmed]; exact Hlt⟩
    try wp_auto
    have hlenc : (s.confirmed.set (sint.nat n) ({ term := ct', index := (if (s.confirmed[sint.nat n]!.term == ct') = true then
          imax s.confirmed[sint.nat n]!.index (f.prevLogIndex + f.entries.length)
          else f.prevLogIndex + f.entries.length) } : Confirmed)).length = NS.cfg.server.length := by
      rw [hNSc, List.length_set, HWf.len_confirmed]
    wp_apply wp_set_confirmed q { NS with msgs := lset.add s.msgs (ackFact s.cfg.server[sint.nat n]! cf' ct'
      (f.prevLogIndex + f.entries.length)) } co _ hlenc $$ [Hq Hco] as Hq
    · iframe Hq Hco
    try wp_auto
    bsp_some
  -- an ack up to the commit index: `f.PrevLogIndex < s.CommitIndex[n] && m.index() == s.CommitIndex[n]`
  rw [ite_eq_right_of_eq_false _ _ (eq_false (by decide))] at Ht
  try wp_auto
  icases intsRO_at g.CommitIndex' s.commitIndex n ⟨Hn, by rw [HWf.len_commitIndex]; exact Hlt⟩ $$ HCommitIndex with ⟨%ci, #Hcia, %Hci⟩
  obtain ⟨x, hx, Ht⟩ := bind_ok Ht
  obtain ⟨y, hy, hyt, hyf⟩ := andM_ok hx
  simp only [pure_ok, Except.ok.injEq] at hy
  subst hy
  wp_apply wp_load_at _ _ ci Hn $$ [Hcia]
  · iexact Hcia
  try wp_auto
  rw [Hgfp.2.2.2.1, Hci]
  by_cases hpc : f.prevLogIndex < s.commitIndex[sint.nat n]!
  case neg =>
    rw [decide_eq_false hpc]
    have := hyf (by simpa using hpc)
    subst this
    rw [ite_eq_left_of_eq_true _ _ (eq_true (by decide))] at Ht
    cases Ht
    bsp_none
  rw [decide_eq_true hpc]
  have hz := hyt (by simpa using hpc)
  obtain ⟨mi2, hmi2, hz⟩ := bind_ok hz
  rw [hmi] at hmi2; cases hmi2
  simp only [pure_ok, Except.ok.injEq] at hz
  subst hz
  try wp_auto
  try rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Msg.TypeAssumptions.ptr_unfold'index.method_unfold]
  try wp_auto
  wp_apply wp_index gm m mi $$ [Hm] as %ui3 %Hui3
  · iframe Hm; ipureintro; exact hmi
  try wp_auto
  wp_apply wp_load_at _ _ ci Hn $$ [Hcia]
  · iexact Hcia
  try wp_auto
  by_cases hic : mi = s.commitIndex[sint.nat n]!
  case neg =>
    rw [decide_eq_false (fun h => hic (by rw [← Hui3, ← Hci]; exact bootSendP_w64_eq.1 h))]
    rw [show (mi == s.commitIndex[sint.nat n]!) = false by simpa using hic] at Ht
    rw [ite_eq_left_of_eq_true _ _ (eq_true (by decide))] at Ht
    cases Ht
    bsp_none
  rw [decide_eq_true (bootSendP_w64_eq.2 (by rw [Hui3, Hci]; exact hic))]
  rw [show (mi == s.commitIndex[sint.nat n]!) = true by simpa using hic] at Ht
  rw [ite_eq_right_of_eq_false _ _ (eq_false (by decide))] at Ht
  obtain ⟨cf', hcf', Ht⟩ := bind_ok Ht
  obtain ⟨ct', hct', Ht⟩ := bind_ok Ht
  cases Ht
  try wp_auto
  try rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Msg.TypeAssumptions.ptr_unfold'from.method_unfold]
  try wp_auto
  wp_apply wp_from gcm cm cf' $$ [Hcm]
  · iframe Hcm; ipureintro; exact hcf'
  try wp_auto
  try rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Msg.TypeAssumptions.ptr_unfold'term.method_unfold]
  try wp_auto
  wp_apply wp_term gcm cm ct' $$ [Hcm] as %ucmt3 %Hucmt3
  · iframe Hcm; ipureintro; exact hct'
  try wp_auto
  wp_apply wp_load_at _ _ ci Hn $$ [Hcia]
  · iexact Hcia
  try wp_auto
  wp_apply wp_AckFact s.cfg.server[sint.nat n]! cf' ucmt3 ci as %ga %Hga
  rw [Hucmt3, Hci] at Hga
  try wp_auto
  wp_apply wp_factsAdd g.Msgs' s.msgs ga _ $$ [HMsgs] as %fo #Hfo
  · iframe HMsgs; ipureintro
    refine ⟨Hga, ?_⟩
    have := HW.msgs_len; omega
  try wp_auto
  wp_apply wp_set_msgs q NS fo _ $$ [Hq Hfo] as Hq
  · iframe Hq Hfo
  try wp_auto
  bsp_some
end proof

end AntCheck
end EtcdGrove
end Perennial

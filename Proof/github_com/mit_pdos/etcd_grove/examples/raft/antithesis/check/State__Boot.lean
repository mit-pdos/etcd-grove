/-
Lean-first (no Rocq counterpart). #33 S3b W5 (2026-11-23): the proof of `State.Boot` (B 162-194).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State__Boot
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State__clone
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.setPre
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.setMsgs
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.setQueue
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.setReads
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.setStr
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Recovered
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State__Vote
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.SubSeq
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Concat
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State__VoteOf
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.setInt
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.setLog
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.setConfirmed
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.factsMinus
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.votesMinus
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Event__has
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Event__applied
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.EntriesEqual
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.ConfOf
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State__InitConf
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.setConf
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.LastConf
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.SameConf
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.StateLaws
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.EvalLaws
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.ActionLaws
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Init0Laws
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.BootSendProofLaws

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

theorem State.Boot.wp_proof
    (wp_clone : State.clone.spec (GF := GF) (hG := hG))
    (wp_setPre : setPre.spec (GF := GF) (hG := hG))
    (wp_setMsgs : setMsgs.spec (GF := GF) (hG := hG))
    (wp_setQueue : setQueue.spec (GF := GF) (hG := hG))
    (wp_setReads : setReads.spec (GF := GF) (hG := hG))
    (wp_setStr : setStr.spec (GF := GF) (hG := hG))
    (wp_Recovered : Recovered.spec (GF := GF) (hG := hG))
    (wp_Vote : State.Vote.spec (GF := GF) (hG := hG))
    (wp_SubSeq : SubSeq.spec (GF := GF) (hG := hG))
    (wp_Concat : Concat.spec (GF := GF) (hG := hG))
    (wp_VoteOf : State.VoteOf.spec (GF := GF) (hG := hG))
    (wp_setInt : setInt.spec (GF := GF) (hG := hG))
    (wp_setLog : setLog.spec (GF := GF) (hG := hG))
    (wp_setConfirmed : setConfirmed.spec (GF := GF) (hG := hG))
    (wp_factsMinus : factsMinus.spec (GF := GF) (hG := hG))
    (wp_votesMinus : votesMinus.spec (GF := GF) (hG := hG))
    (wp_has : Event.has.spec (GF := GF) (hG := hG))
    (wp_applied : Event.applied.spec (GF := GF) (hG := hG))
    (wp_EntriesEqual : EntriesEqual.spec (GF := GF) (hG := hG))
    (wp_ConfOf : ConfOf.spec (GF := GF) (hG := hG))
    (wp_InitConf : State.InitConf.spec (GF := GF) (hG := hG))
    (wp_setConf : setConf.spec (GF := GF) (hG := hG))
    (wp_LastConf : LastConf.spec (GF := GF) (hG := hG))
    (wp_SameConf : SameConf.spec (GF := GF) (hG := hG)) :
    State.Boot.spec (GF := GF) (hG := hG) := by
  intro p s n e ev o
  wp_start as ⟨#Hs, #He, %Hn, %Hlt, %HBd, %Ho⟩
  ihave #Hs' := Hs
  iunfold stateRO at Hs'
  iNamed Hs'
  iNamed Hf
  iStructNamed Hp
  obtain ⟨bb, EE, HW, HNO, HCh, hbb, hEE⟩ := HBd
  unfold numBound Event.weight at hbb
  unfold State.boot at Ho
  wp_auto
  wp_apply wp_clone p s $$ [Hs] as %q Hq
  · iexact Hs
  try wp_auto
  wp_apply wp_setPre g.Undo' s.undo n null none $$ [HUndo] as %uo #Huo
  · iframe HUndo; iunfold preRO; ipureintro; exact ⟨rfl, Hn, by rw [HWf.len_undo]; exact Hlt⟩
  try wp_auto
  wp_apply wp_set_undo q s uo (s.undo.set (sint.nat n) none) (by rw [List.length_set, HWf.len_undo]) $$ [Hq Huo] as Hq
  · iframe Hq Huo
  try wp_auto
  ihave #Hnil1 := Init0_msgsNil (GF := GF)
  wp_apply wp_setMsgs g.Pending' s.pending n slice.nil [] $$ [HPending Hnil1] as %po #Hpo
  · iframe HPending Hnil1; ipureintro; exact ⟨Hn, by rw [HWf.len_pending]; exact Hlt⟩
  try wp_auto
  wp_apply wp_set_pending q { s with undo := s.undo.set (sint.nat n) none } po (s.pending.set (sint.nat n) []) (by rw [List.length_set, HWf.len_pending]) $$ [Hq Hpo] as Hq
  · iframe Hq Hpo
  try wp_auto
  ihave #Hnil2 := Init0_qitemsNil (GF := GF)
  wp_apply wp_setQueue g.Queue' s.queue n slice.nil [] $$ [HQueue Hnil2] as %quo #Hquo
  · iframe HQueue Hnil2; ipureintro; exact ⟨Hn, by rw [HWf.len_queue]; exact Hlt⟩
  try wp_auto
  wp_apply wp_set_queue q { s with undo := s.undo.set (sint.nat n) none, pending := s.pending.set (sint.nat n) [] } quo (s.queue.set (sint.nat n) []) (by rw [List.length_set, HWf.len_queue]) $$ [Hq Hquo] as Hq
  · iframe Hq Hquo
  try wp_auto
  ihave #Hnil3 := Init0_readRecsNil (GF := GF)
  wp_apply wp_setReads g.Reads' s.reads n slice.nil [] $$ [HReads Hnil3] as %ro #Hro
  · iframe HReads Hnil3; ipureintro; exact ⟨Hn, by rw [HWf.len_reads]; exact Hlt⟩
  try wp_auto
  wp_apply wp_set_reads q { s with undo := s.undo.set (sint.nat n) none, pending := s.pending.set (sint.nat n) [], queue := s.queue.set (sint.nat n) [] } ro (s.reads.set (sint.nat n) []) (by rw [List.length_set, HWf.len_reads]) $$ [Hq Hro] as Hq
  · iframe Hq Hro
  try wp_auto
  try rw [show (github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Follower : val) = #follower from rfl]
  try wp_auto
  wp_apply wp_setStr g.Role' s.role n follower $$ [HRole] as %rlo #Hrlo
  · iframe HRole; ipureintro; exact ⟨Hn, by rw [HWf.len_role]; exact Hlt⟩
  try wp_auto
  wp_apply wp_set_role q { s with undo := s.undo.set (sint.nat n) none, pending := s.pending.set (sint.nat n) [], queue := s.queue.set (sint.nat n) [], reads := s.reads.set (sint.nat n) [] } rlo (s.role.set (sint.nat n) follower) (by rw [List.length_set, HWf.len_role]) $$ [Hq Hrlo] as Hq
  · iframe Hq Hrlo
  ihave Hq : stateOwn q ({ s with undo := s.undo.set (sint.nat n) none, pending := s.pending.set (sint.nat n) [], queue := s.queue.set (sint.nat n) [], reads := s.reads.set (sint.nat n) [], role := s.role.set (sint.nat n) follower } : State) $$ [Hq]
  · iexact Hq
  try wp_auto
  icases intsRO_at g.CurrentTerm' s.currentTerm n ⟨Hn, by rw [HWf.len_currentTerm]; exact Hlt⟩ $$ HCurrentTerm with ⟨%ct, #Hcta, %Hct⟩
  icases intsRO_at g.CommitIndex' s.commitIndex n ⟨Hn, by rw [HWf.len_commitIndex]; exact Hlt⟩ $$ HCommitIndex with ⟨%ci, #Hcia, %Hci⟩
  icases logsRO_at g.Log' s.log n ⟨Hn, by rw [HWf.len_log]; exact Hlt⟩ $$ HLog with ⟨%lg, #Hlga, #Hlg⟩
  ihave %Hlgl := logRO_len _ _ $$ Hlg
  obtain ⟨r, hr, Ho⟩ := bind_ok Ho
  wp_apply wp_load_at _ _ ct Hn $$ [Hcta]
  · iexact Hcta
  try wp_auto
  wp_apply wp_Vote p s n $$ [Hs]
  · iframe Hs; ipureintro; exact ⟨Hn, Hlt⟩
  try wp_auto
  wp_apply wp_load_at _ _ ci Hn $$ [Hcia]
  · iexact Hcia
  try wp_auto
  wp_apply wp_load_at _ _ lg Hn $$ [Hlga]
  · iexact Hlga
  try wp_auto
  wp_apply wp_Recovered e ev ct _ ci lg _ r $$ [He Hlg]
  · iframe He Hlg; ipureintro; rw [Hct, Hci]; exact hr
  dsimp only at Ho
  have hlog0 : logWithin bb EE (s.log[sint.nat n]!) :=
    getElem!_mem' (α := List Entry) (P := fun l => logWithin bb EE l) HW.log ⟨Nat.zero_le _, fun x hx => by cases hx⟩
  wp_join (Q := fun v => iprop(s_ptr ↦ p ∗ ev_ptr ↦ e ∗ n_ptr ↦ n ∗ ns_ptr ↦ q ∗
      ((⌜v = executeVal⌝ ∗ «$res0_ptr» ↦ zero_val Loc ∗ «$res1_ptr» ↦ zero_val Bool ∗
          ∃ NS : State, stateOwn q NS ∗ ⌜bootSendP_bootTail s NS (sint.nat n) ev = .ok o ∧ NS.cfg = s.cfg ∧
            logWithin bb EE (NS.log[sint.nat n]!)⌝) ∨
       (⌜v = returnVal #()⌝ ∗ ⌜o = none⌝ ∗ ∃ v0 : Loc, «$res0_ptr» ↦ v0 ∗ «$res1_ptr» ↦ false))))
    at next with [s ev n ns «$res0» «$res1» Hq]
  · cases r
    case true =>
      have Ht : bootSendP_bootTail s ({ s with undo := s.undo.set (sint.nat n) none, pending := s.pending.set (sint.nat n) [], queue := s.queue.set (sint.nat n) [], reads := s.reads.set (sint.nat n) [], role := s.role.set (sint.nat n) follower } : State) (sint.nat n) ev = .ok o := by
        rw [ite_eq_right_of_eq_false _ _ (eq_false (by decide))] at Ho
        unfold bootSendP_bootTail
        exact Ho
      try wp_auto
      iframe s ev n ns
      ileft
      iframe «$res0» «$res1»
      isplitr
      · ipureintro; rfl
      iexists _
      iframe Hq
      ipureintro
      exact ⟨Ht, rfl, hlog0⟩
    -- not recovered: the write `s.Undo[n]` restored
    rw [ite_eq_left_of_eq_true _ _ (eq_true (by decide))] at Ho
    icases undoRO_at g.Undo' s.undo n ⟨Hn, by rw [HWf.len_undo]; exact Hlt⟩ $$ HUndo with ⟨%u, #Hua, #Hu⟩
    try wp_auto
    wp_apply wp_load_at _ _ u Hn $$ [Hua]
    · iexact Hua
    cases hu : s.undo[sint.nat n]! with
    | none =>
      rw [hu] at Ho
      cases Ho
      iunfold preRO at Hu
      icases Hu with %Hnull
      subst Hnull
      try wp_auto
      iframe s ev n ns
      iright
      isplitr
      · ipureintro; rfl
      isplitr
      · ipureintro; rfl
      iexists _
      iframe
    | some pu =>
      rw [hu] at Ho
      iunfold preRO at Hu
      icases Hu with ⟨%gp, #Hgp, %Hpf, #Hsuf, #Hms, #Hvs, #-⟩
      obtain ⟨ht, hvt, hvf, hcm, hkp, hcf, -, hmd⟩ := Hpf
      ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hgp
      wp_if_destruct
      · exact absurd rfl Hnn
      wp_apply wp_load_at _ _ u Hn $$ [Hua]
      · iexact Hua
      try wp_auto
      iStructNamed Hgp
      try wp_auto
      dsimp only at Ho
      rw [hmd]
      cases hm : pu.made
      · rw [hm] at Ho
        rw [ite_eq_right_of_eq_false _ _ (eq_false (by decide))] at Ho
        try wp_auto
        -- `l := Concat(SubSeq(s.Log[n], 1, u.Keep), u.Suffix)`
        obtain ⟨pre, hpre, Ho⟩ := bind_ok Ho
        obtain ⟨r2, hr2, Ho⟩ := bind_ok Ho
        have huw : pu.Within bb EE := HW.undo _ (getElem!_some_mem hu) pu rfl
        have hpl := bootSend_subSeq_one_length hpre
        have hlogR := bootSendP_restored_log HW hu hpre
        wp_apply wp_load_at _ _ lg Hn $$ [Hlga]
        · iexact Hlga
        try wp_auto
        wp_apply wp_SubSeq lg _ (W64 1) gp.Keep' pre $$ [Hlg] as %prl #Hpre
        · iframe Hlg; ipureintro; rw [sint_one, hkp]; exact hpre
        try wp_auto
        wp_apply wp_Concat prl pre gp.Suffix' pu.suffix $$ [Hpre Hsuf] as %ll #Hll
        · iframe Hpre Hsuf; ipureintro
          have := huw.2.2.2.1; have := huw.2.2.2.2.2.2.2.1.1; unfold bigOk at *; omega
        try wp_auto
        wp_apply wp_VoteOf p s gp.VoteTerm' gp.VoteFor' gp.Term' $$ [Hs]
        · iexact Hs
        try wp_auto
        wp_apply wp_Recovered e ev gp.Term' _ gp.Commit' ll _ r2 $$ [He Hll]
        · iframe He Hll; ipureintro; rw [ht, hvt, hvf, hcm]; exact hr2
        try wp_auto
        cases r2
        · try wp_auto
          iframe s ev n ns
          iright
          isplitr
          · ipureintro; rfl
          isplitr
          · ipureintro
            rw [ite_eq_left_of_eq_true _ _ (eq_true (by decide))] at Ho
            cases Ho; rfl
          iexists _
          iframe
        rw [ite_eq_right_of_eq_false _ _ (eq_false (by decide))] at Ho
        try wp_auto
        wp_apply wp_setInt g.CurrentTerm' s.currentTerm n gp.Term' $$ [HCurrentTerm] as %x0 #Hx0
        · iframe HCurrentTerm; ipureintro; exact ⟨Hn, by rw [HWf.len_currentTerm]; exact Hlt⟩
        try wp_auto
        wp_apply wp_set_currentTerm q ({ s with undo := s.undo.set (sint.nat n) none, pending := s.pending.set (sint.nat n) [], queue := s.queue.set (sint.nat n) [], reads := s.reads.set (sint.nat n) [], role := s.role.set (sint.nat n) follower } : State) x0 (s.currentTerm.set (sint.nat n) (sint.Z gp.Term')) (by rw [List.length_set, HWf.len_currentTerm]) $$ [Hq Hx0] as Hq
        · iframe Hq Hx0
        try wp_auto
        wp_apply wp_setInt g.VoteTerm' s.voteTerm n gp.VoteTerm' $$ [HVoteTerm] as %x1 #Hx1
        · iframe HVoteTerm; ipureintro; exact ⟨Hn, by rw [HWf.len_voteTerm]; exact Hlt⟩
        try wp_auto
        wp_apply wp_set_voteTerm q ({ s with undo := s.undo.set (sint.nat n) none, pending := s.pending.set (sint.nat n) [], queue := s.queue.set (sint.nat n) [], reads := s.reads.set (sint.nat n) [], role := s.role.set (sint.nat n) follower, currentTerm := s.currentTerm.set (sint.nat n) (sint.Z gp.Term') } : State) x1 (s.voteTerm.set (sint.nat n) (sint.Z gp.VoteTerm')) (by rw [List.length_set, HWf.len_voteTerm]) $$ [Hq Hx1] as Hq
        · iframe Hq Hx1
        try wp_auto
        wp_apply wp_setStr g.VoteFor' s.voteFor n gp.VoteFor' $$ [HVoteFor] as %x2 #Hx2
        · iframe HVoteFor; ipureintro; exact ⟨Hn, by rw [HWf.len_voteFor]; exact Hlt⟩
        try wp_auto
        wp_apply wp_set_voteFor q ({ s with undo := s.undo.set (sint.nat n) none, pending := s.pending.set (sint.nat n) [], queue := s.queue.set (sint.nat n) [], reads := s.reads.set (sint.nat n) [], role := s.role.set (sint.nat n) follower, currentTerm := s.currentTerm.set (sint.nat n) (sint.Z gp.Term'), voteTerm := s.voteTerm.set (sint.nat n) (sint.Z gp.VoteTerm') } : State) x2 (s.voteFor.set (sint.nat n) gp.VoteFor') (by rw [List.length_set, HWf.len_voteFor]) $$ [Hq Hx2] as Hq
        · iframe Hq Hx2
        try wp_auto
        wp_apply wp_setInt g.CommitIndex' s.commitIndex n gp.Commit' $$ [HCommitIndex] as %x3 #Hx3
        · iframe HCommitIndex; ipureintro; exact ⟨Hn, by rw [HWf.len_commitIndex]; exact Hlt⟩
        try wp_auto
        wp_apply wp_set_commitIndex q ({ s with undo := s.undo.set (sint.nat n) none, pending := s.pending.set (sint.nat n) [], queue := s.queue.set (sint.nat n) [], reads := s.reads.set (sint.nat n) [], role := s.role.set (sint.nat n) follower, currentTerm := s.currentTerm.set (sint.nat n) (sint.Z gp.Term'), voteTerm := s.voteTerm.set (sint.nat n) (sint.Z gp.VoteTerm'), voteFor := s.voteFor.set (sint.nat n) gp.VoteFor' } : State) x3 (s.commitIndex.set (sint.nat n) (sint.Z gp.Commit')) (by rw [List.length_set, HWf.len_commitIndex]) $$ [Hq Hx3] as Hq
        · iframe Hq Hx3
        try wp_auto
        wp_apply wp_setLog g.Log' s.log n ll (pre ++ pu.suffix) $$ [HLog Hll] as %x4 #Hx4
        · iframe HLog Hll; ipureintro; exact ⟨Hn, by rw [HWf.len_log]; exact Hlt⟩
        try wp_auto
        wp_apply wp_set_log q ({ s with undo := s.undo.set (sint.nat n) none, pending := s.pending.set (sint.nat n) [], queue := s.queue.set (sint.nat n) [], reads := s.reads.set (sint.nat n) [], role := s.role.set (sint.nat n) follower, currentTerm := s.currentTerm.set (sint.nat n) (sint.Z gp.Term'), voteTerm := s.voteTerm.set (sint.nat n) (sint.Z gp.VoteTerm'), voteFor := s.voteFor.set (sint.nat n) gp.VoteFor', commitIndex := s.commitIndex.set (sint.nat n) (sint.Z gp.Commit') } : State) x4 (s.log.set (sint.nat n) (pre ++ pu.suffix)) (by rw [List.length_set, HWf.len_log]) $$ [Hq Hx4] as Hq
        · iframe Hq Hx4
        try wp_auto
        wp_apply wp_setConfirmed g.Confirmed' s.confirmed n gp.Confirmed' pu.confirmed $$ [HConfirmed] as %x5 #Hx5
        · iframe HConfirmed; ipureintro; exact ⟨hcf, Hn, by rw [HWf.len_confirmed]; exact Hlt⟩
        try wp_auto
        wp_apply wp_set_confirmed q ({ s with undo := s.undo.set (sint.nat n) none, pending := s.pending.set (sint.nat n) [], queue := s.queue.set (sint.nat n) [], reads := s.reads.set (sint.nat n) [], role := s.role.set (sint.nat n) follower, currentTerm := s.currentTerm.set (sint.nat n) (sint.Z gp.Term'), voteTerm := s.voteTerm.set (sint.nat n) (sint.Z gp.VoteTerm'), voteFor := s.voteFor.set (sint.nat n) gp.VoteFor', commitIndex := s.commitIndex.set (sint.nat n) (sint.Z gp.Commit'), log := s.log.set (sint.nat n) (pre ++ pu.suffix) } : State) x5 (s.confirmed.set (sint.nat n) pu.confirmed) (by rw [List.length_set, HWf.len_confirmed]) $$ [Hq Hx5] as Hq
        · iframe Hq Hx5
        try wp_auto
        wp_apply wp_factsMinus g.Msgs' s.msgs gp.Msgs' pu.msgs $$ [HMsgs Hms] as %x6 #Hx6
        · iframe HMsgs Hms
        try wp_auto
        wp_apply wp_set_msgs q ({ s with undo := s.undo.set (sint.nat n) none, pending := s.pending.set (sint.nat n) [], queue := s.queue.set (sint.nat n) [], reads := s.reads.set (sint.nat n) [], role := s.role.set (sint.nat n) follower, currentTerm := s.currentTerm.set (sint.nat n) (sint.Z gp.Term'), voteTerm := s.voteTerm.set (sint.nat n) (sint.Z gp.VoteTerm'), voteFor := s.voteFor.set (sint.nat n) gp.VoteFor', commitIndex := s.commitIndex.set (sint.nat n) (sint.Z gp.Commit'), log := s.log.set (sint.nat n) (pre ++ pu.suffix), confirmed := s.confirmed.set (sint.nat n) pu.confirmed } : State) x6 (lset.minus s.msgs pu.msgs) $$ [Hq Hx6] as Hq
        · iframe Hq Hx6
        try wp_auto
        wp_apply wp_votesMinus g.Votes' s.votes gp.Votes' pu.votes $$ [HVotes Hvs] as %x7 #Hx7
        · iframe HVotes Hvs
        try wp_auto
        wp_apply wp_set_votes q ({ s with undo := s.undo.set (sint.nat n) none, pending := s.pending.set (sint.nat n) [], queue := s.queue.set (sint.nat n) [], reads := s.reads.set (sint.nat n) [], role := s.role.set (sint.nat n) follower, currentTerm := s.currentTerm.set (sint.nat n) (sint.Z gp.Term'), voteTerm := s.voteTerm.set (sint.nat n) (sint.Z gp.VoteTerm'), voteFor := s.voteFor.set (sint.nat n) gp.VoteFor', commitIndex := s.commitIndex.set (sint.nat n) (sint.Z gp.Commit'), log := s.log.set (sint.nat n) (pre ++ pu.suffix), confirmed := s.confirmed.set (sint.nat n) pu.confirmed, msgs := lset.minus s.msgs pu.msgs } : State) x7 (lset.minus s.votes pu.votes) $$ [Hq Hx7] as Hq
        · iframe Hq Hx7
        try wp_auto
        iframe s ev n ns
        ileft
        iframe «$res0» «$res1»
        isplitr
        · ipureintro; rfl
        iexists _
        iframe Hq
        ipureintro
        refine ⟨?_, rfl, ?_⟩
        · unfold bootSendP_bootTail
          rw [ht, hvt, hvf, hcm]
          exact Ho
        · show logWithin bb EE ((s.log.set (sint.nat n) (pre ++ pu.suffix))[sint.nat n]!)
          have hl : sint.nat n < s.log.length := by rw [HWf.len_log]; have := sint_nat_cast Hn; omega
          rw [List.getElem!_eq_getElem?_getD, List.getElem?_set_self hl]; exact hlogR
      · try wp_auto
        iframe s ev n ns
        iright
        isplitr
        · ipureintro; rfl
        isplitr
        · ipureintro; rw [hm] at Ho; cases Ho; rfl
        iexists _
        iframe
  iintro ⟨s, ev, n, ns, Hv⟩
  icases Hv with (⟨%Hv, «$res0», «$res1», %NS, Hq, %HNS⟩ | ⟨%Hv, %Hon, %v0, «$res0», «$res1»⟩)
  rotate_left
  · subst Hv Hon
    try wp_auto
    iapply HΦ; iunfold succOwn; ipureintro; rfl
  subst Hv
  obtain ⟨Ht, hcfg, hlogn⟩ := HNS
  obtain ⟨a, ha, Ht⟩ := bootSendP_bootTail_ok Ht
  have han : numOk a := by
    by_cases hap : ev.applied.isSome = true
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hap)] at ha
      have := HNO.2.2.2.2.2.1; rw [need_ok ha] at this; exact this
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hap)] at ha
      cases ha; unfold numOk numBound; omega
  unfold numOk numBound at han
  try wp_auto
  wp_join iprop(∃ ua : w64, a_ptr ↦ ua ∗ ev_ptr ↦ e ∗ ⌜sint.Z ua = a⌝) at next with [a ev] as ⟨%ua, a, ev, %Hua⟩
  · rw [show (github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.FApplied : val) = #fApplied from rfl]
    wp_apply wp_has e ev fApplied ev.applied.isSome $$ [He]
    · iframe He; ipureintro; exact Event.hasF_Applied _
    by_cases hap : ev.applied.isSome = true
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hap)] at ha
      rw [hap]
      try wp_auto
      wp_apply wp_applied e ev a $$ [He] as %ua %Hua
      · iframe He; ipureintro; exact ha
      try wp_auto
      wp_join_done
      iexists ua; iframe a ev; ipureintro; exact Hua
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hap)] at ha
      cases ha
      rw [Bool.eq_false_of_ne_true hap]
      try wp_auto
      wp_join_done
      iexists _; iframe a ev; ipureintro; rfl
  -- `logn := ns.Log[n]`
  icases bootSendP_stateOwn_log q NS $$ Hq with ⟨%gq, Hqp, #HqLog, %HqWf, Hqc⟩
  icases logsRO_at gq.Log' NS.log n ⟨Hn, by rw [HqWf.len_log, hcfg]; exact Hlt⟩ $$ HqLog with ⟨%lgn, #Hlgna, #Hlgn⟩
  ihave %Hlgnl := logRO_len _ _ $$ Hlgn
  ihave %Hchl := logRO_len _ _ $$ HChain
  try wp_auto
  wp_apply wp_load_at _ _ lgn Hn $$ [Hlgna]
  · iexact Hlgna
  ihave Hq := Hqc $$ Hqp
  try wp_auto
  -- `a == 0 || (a <= len(logn) && a <= len(s.Chain) && EntriesEqual(...))`
  unfold bootSendP_bootRest at Ht
  dsimp only at Ht
  obtain ⟨ok1, hok1, Ht⟩ := bind_ok Ht
  obtain ⟨x0, hx0, hx0t, hx0f⟩ := orM_ok hok1
  simp only [pure_ok, Except.ok.injEq] at hx0
  subst hx0
  wp_join (Q := fun v => iprop(⌜v = #ok1⌝ ∗ a_ptr ↦ ua ∗ s_ptr ↦ p ∗ logn_ptr ↦ lgn)) at (if: _ then #true else _) with [a s logn] as ⟨%Hv, a, s, logn⟩
  · by_cases ha0 : a = 0
    · rw [decide_eq_true ((bootSendP_w64_eq_zero).2 (by rw [Hua]; exact ha0))]
      have : ok1 = true := hx0t (by simp [ha0])
      subst this
      try wp_auto
      iframe; ipureintro; rfl
    rw [decide_eq_false (fun h => ha0 (by rw [← Hua]; exact (bootSendP_w64_eq_zero).1 h))]
    have hb := hx0f (by simp [ha0])
    obtain ⟨y, hy, hyt, hyf⟩ := andM_ok hb
    simp only [pure_ok, Except.ok.injEq] at hy
    subst hy
    try wp_auto
    rw [Hua, Hlgnl]
    by_cases hb1 : a ≤ (NS.log[sint.nat n]!).length
    case neg =>
      rw [decide_eq_false hb1]
      have : ok1 = false := hyf (by simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]; exact .inl hb1)
      subst this
      try wp_auto
      iframe; ipureintro; rfl
    rw [decide_eq_true hb1]
    try wp_auto
    rw [Hua, Hchl]
    by_cases hb2 : a ≤ s.chain.length
    case neg =>
      rw [decide_eq_false hb2]
      have : ok1 = false := hyf (by simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]; exact .inr hb2)
      subst this
      try wp_auto
      iframe; ipureintro; rfl
    rw [decide_eq_true hb2]
    have hc := hyt (by simp only [Bool.and_eq_true, decide_eq_true_eq]; exact ⟨hb1, hb2⟩)
    obtain ⟨sc, hsc, hc⟩ := bind_ok hc
    obtain ⟨sl, hsl, hc⟩ := bind_ok hc
    try wp_auto
    wp_apply wp_SubSeq g.Chain' s.chain (W64 1) ua sc $$ [HChain] as %scl #Hsc
    · iframe HChain; ipureintro; rw [Hua, sint_one]; exact hsc
    try wp_auto
    wp_apply wp_SubSeq lgn _ (W64 1) ua sl $$ [Hlgn] as %sll #Hsl
    · iframe Hlgn; ipureintro; rw [Hua, sint_one]; exact hsl
    try wp_auto
    wp_apply wp_EntriesEqual scl sc sll sl ok1 $$ [Hsc Hsl]
    · iframe Hsc Hsl; ipureintro; exact hc
    try wp_auto
    iframe; ipureintro; rfl
  subst Hv
  try wp_auto
  cases ok1
  · simp only [Bool.not_false, ite_true, pure_ok, Except.ok.injEq] at Ht
    subst Ht
    try wp_auto
    iapply HΦ; iunfold succOwn; ipureintro; rfl
  simp only [Bool.not_true, Bool.false_eq_true, ite_false] at Ht
  obtain ⟨c, hc, Ht⟩ := bind_ok Ht
  obtain ⟨lc, hlc, Ht⟩ := bind_ok Ht
  obtain ⟨sm, hsm, Ht⟩ := bind_ok Ht
  try wp_auto
  -- `ns.LastApplied = setInt(s.LastApplied, n, a)`
  wp_apply wp_setInt g.LastApplied' s.lastApplied n ua $$ [HLastApplied] as %lao #Hlao
  · iframe HLastApplied; ipureintro; exact ⟨Hn, by rw [HWf.len_lastApplied]; exact Hlt⟩
  try wp_auto
  wp_apply wp_set_lastApplied q NS lao (s.lastApplied.set (sint.nat n) (sint.Z ua)) (by rw [List.length_set, HWf.len_lastApplied, hcfg]) $$ [Hq Hlao] as Hq
  · iframe Hq Hlao
  try wp_auto
  -- `c := ConfOf(logn, a, s.InitConf())`
  wp_apply wp_InitConf p s $$ [Hs] as %ic #Hic
  · iexact Hs
  try wp_auto
  wp_apply wp_ConfOf lgn _ ua ic s.initConf c $$ [Hlgn Hic] as %gc #Hgc
  · iframe Hlgn Hic; ipureintro; exact ⟨by rw [Hua]; exact hc, by omega, bootSendP_confOf_bounded hlogn hEE⟩
  try wp_auto
  wp_apply wp_setConf g.Config' s.config n gc c $$ [HConfig Hgc] as %co #Hco
  · iframe HConfig Hgc; ipureintro; exact ⟨Hn, by rw [HWf.len_config]; exact Hlt⟩
  try wp_auto
  wp_apply wp_set_config q { NS with lastApplied := s.lastApplied.set (sint.nat n) (sint.Z ua) } co (s.config.set (sint.nat n) c) (by rw [List.length_set, HWf.len_config]; exact hcfg.symm ▸ rfl) $$ [Hq Hco] as Hq
  · iframe Hq Hco
  try wp_auto
  -- `ns.ConfAt = setInt(s.ConfAt, n, LastConf(logn, a))`
  wp_apply wp_LastConf lgn _ ua lc $$ [Hlgn] as %wlc %Hwlc
  · iframe Hlgn; ipureintro; exact ⟨by rw [Hua]; exact hlc, by omega⟩
  try wp_auto
  wp_apply wp_setInt g.ConfAt' s.confAt n wlc $$ [HConfAt] as %cao #Hcao
  · iframe HConfAt; ipureintro; exact ⟨Hn, by rw [HWf.len_confAt]; exact Hlt⟩
  try wp_auto
  wp_apply wp_set_confAt q { { NS with lastApplied := s.lastApplied.set (sint.nat n) (sint.Z ua) } with config := s.config.set (sint.nat n) c } cao (s.confAt.set (sint.nat n) (sint.Z wlc)) (by rw [List.length_set, HWf.len_confAt]; exact hcfg.symm ▸ rfl) $$ [Hq Hcao] as Hq
  · iframe Hq Hcao
  try wp_auto
  -- `SameConf(ev, c)`
  wp_apply wp_SameConf e ev gc c sm $$ [He Hgc]
  · iframe He Hgc; ipureintro; exact ⟨hsm, by omega⟩
  cases sm
  · simp only [Bool.not_false, ite_true, pure_ok, Except.ok.injEq] at Ht
    subst Ht
    try wp_auto
    iapply HΦ; iunfold succOwn; ipureintro; rfl
  simp only [Bool.not_true, Bool.false_eq_true, ite_false, pure_ok, Except.ok.injEq] at Ht
  subst Ht
  try wp_auto
  rw [Hua, Hwlc]
  iapply HΦ
  iunfold succOwn
  isplitr
  · ipureintro; rfl
  iexact Hq
end proof

end AntCheck
end EtcdGrove
end Perennial

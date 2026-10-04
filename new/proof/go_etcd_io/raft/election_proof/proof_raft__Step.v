(** The per-message-type lemmas are **proof structure, not
    specification**.  [Step] is one Go function and therefore has exactly one
    spec, in [spec_raft__Step.v]; giving each branch its own [Module Type]
    would put several Hoare triples for [r.Step] in several files, which is
    the thing this layout exists to prevent.  Since 2026-09-17 the branches
    live in files of their own -- functors over [STEP_POSTULATES] with no
    signature -- so that [make -j] checks them in parallel; only this file
    may [Require] them, and the ascription below is still the only thing any
    other file can see.

    Since 2026-09-18 those files sit in **[proof_raft__Step_helpers/]**,
    because [Step] is the only function here whose proof needs more than one
    file and having them at the top level broke the four-files-per-function
    pattern the election directory is meant to be audited by.  The directory
    is [proof_<fn>_helpers/] and not [proof_<fn>/] because the latter would
    collide with this file in Rocq's logical namespace.
    [etc/check-module-discipline.py] enforces both halves: a helper at the
    top level is an error, and a [Module Type] inside a helpers directory is
    an error.

    **The replication branches (2026-10-02).**  [MsgProp] is
    [proof_raft__Step_MsgProp.v]; [MsgApp], [MsgHeartbeat], [MsgAppResp],
    [MsgHeartbeatResp] and [MsgBeat] were written in parallel against
    statements fixed in advance, so this file's dispatch for each of them
    is a lemma ([dispatch_App], ...) that takes the branch lemma, at that
    statement, as a hypothesis, and [wp_raft__Step] applies it to the
    branch.  The ghost-side work -- deriving each branch's protocol
    premises from [own_raft_ghost] and [is_message], and taking
    [own_raft_ghost_step] with the branch's [recv] -- is in those lemmas. *)

Require Export New.proof.go_etcd_io.raft.election_proof.proof_raft__Step_helpers.proof_raft__Step_MsgHup.
Require Export New.proof.go_etcd_io.raft.election_proof.proof_raft__Step_helpers.proof_raft__Step_MsgVote.
Require Export New.proof.go_etcd_io.raft.election_proof.proof_raft__Step_helpers.proof_raft__Step_MsgVoteResp.
Require Export New.proof.go_etcd_io.raft.election_proof.proof_raft__Step_helpers.proof_raft__Step_MsgProp.
Require Export New.proof.go_etcd_io.raft.election_proof.proof_raft__Step_helpers.proof_raft__Step_MsgApp.
Require Export New.proof.go_etcd_io.raft.election_proof.proof_raft__Step_helpers.proof_raft__Step_MsgHeartbeat.
Require Export New.proof.go_etcd_io.raft.election_proof.proof_raft__Step_helpers.proof_raft__Step_MsgAppResp.
Require Export New.proof.go_etcd_io.raft.election_proof.proof_raft__Step_helpers.proof_raft__Step_MsgHeartbeatResp.
Require Export New.proof.go_etcd_io.raft.election_proof.proof_raft__Step_helpers.proof_raft__Step_MsgBeat.
Require Export New.proof.go_etcd_io.raft.election_proof.proof_raft__Step_helpers.proof_raft__Step_MsgSnap.
Require Export New.proof.go_etcd_io.raft.election_proof.proof_raft__Step_helpers.proof_raft__Step_MsgPreVote.
Require Export New.proof.go_etcd_io.raft.election_proof.proof_raft__Step_helpers.proof_raft__Step_MsgPreVoteResp.

Module StepProof (P : STEP_POSTULATES) : STEP.

Module H := StepMsgHup P.
Module V := StepMsgVote P.
Module R := StepMsgVoteResp P.
Module M := StepMsgProp P.
Module A := StepMsgApp P.
Module HB := StepMsgHeartbeat P.
Module AR := StepMsgAppResp P.
Module HR := StepMsgHeartbeatResp P.
Module B := StepMsgBeat P.
Module SN := StepMsgSnap P.
Module PV := StepMsgPreVote P.
Module PR := StepMsgPreVoteResp P.

Section dispatch.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : raft.Assumptions}.
Collection W := sem + package_sem.
Set Default Proof Using "W".

Implicit Type γ : raft_election_names.
Implicit Type s : nstate.t.

(** What [wp_raft__Step]'s postcondition hands to [Φ]: the continuation
    every dispatch lemma below ends in. *)
Definition step_post γ cfg r id (ps : pstate.t) (m : raftpb.Message.t)
    (Φ : val → iProp Σ) : iProp Σ :=
  ∀ (err : error.t) s' ps',
    ("Hphys" ∷ own_raft_phys cfg r id s' ∗
     "Hghost" ∷ own_raft_ghost γ id ps' ∗
     "%Hrel" ∷ ⌜ nstate_rel s' ps' ⌝ ∗
     "%Hrefines" ∷ ⌜ ∃ recv, step cfg id ps recv ps' ⌝ ∗
     "Herr" ∷ (⌜ err = interface.nil ⌝ ∨
               (⌜ m.(raftpb.Message.Type') = MsgProp ⌝ ∗
                (global_addr raft.ErrProposalDropped) ↦□ err))) -∗ Φ #err.

(** The one ghost update of a branch: [recv] is the incoming message, some
    number of times, and that message is [is_message]. *)
Lemma ghost_step_recv γ cfg id (ps ps' : pstate.t) (a : msg.t) recv :
  γ.(re_cfg) = cfg →
  (∀ m', m' ∈ recv → m' = a) →
  step cfg id ps recv ps' →
  is_message γ a -∗ own_raft_ghost γ id ps ={⊤}=∗ own_raft_ghost γ id ps'.
Proof.
  intros <- Hrecv Hstep. iIntros "#Hm Hg".
  iApply (own_raft_ghost_step _ _ _ _ _ Hstep with "[] Hg").
  iApply big_sepL_intro. iIntros "!> %k %m' %Hk".
  rewrite (Hrecv m'); [iFrame "#"|by eapply list_elem_of_lookup_2].
Qed.

(** A branch's postcondition, delivered: the ghost step, then [Φ]. *)
Lemma finish_branch γ cfg r id s s' (m : raftpb.Message.t) (a : msg.t) recv
    (err : error.t) (Φ : val → iProp Σ) :
  γ.(re_cfg) = cfg →
  nstate_wf s' →
  (∀ m', m' ∈ recv → m' = a) →
  step cfg id (to_pstate s) recv (to_pstate s') →
  is_message γ a -∗
  own_raft_ghost γ id (to_pstate s) -∗
  own_raft_phys cfg r id s' -∗
  (⌜ err = interface.nil ⌝ ∨
   (⌜ m.(raftpb.Message.Type') = MsgProp ⌝ ∗ (global_addr raft.ErrProposalDropped) ↦□ err)) -∗
  step_post γ cfg r id (to_pstate s) m Φ -∗
  |={⊤}=> Φ #err.
Proof.
  iIntros (Hcfg Hwf' Hrecv Hstep) "#Hm Hghost Hphys Herr HΦ".
  iMod (ghost_step_recv _ _ _ _ _ _ _ Hcfg Hrecv Hstep with "Hm Hghost") as "Hghost".
  iModIntro. iApply ("HΦ" $! err s' (to_pstate s')). iFrame.
  iPureIntro. split; [split; [done|exact Hwf']|]. by eexists recv.
Qed.

(** The same, for a branch that consumed nothing. *)
Lemma finish_branch0 γ cfg r id s s' (m : raftpb.Message.t) (err : error.t)
    (Φ : val → iProp Σ) :
  γ.(re_cfg) = cfg →
  nstate_wf s' →
  step cfg id (to_pstate s) [] (to_pstate s') →
  own_raft_ghost γ id (to_pstate s) -∗
  own_raft_phys cfg r id s' -∗
  (⌜ err = interface.nil ⌝ ∨
   (⌜ m.(raftpb.Message.Type') = MsgProp ⌝ ∗ (global_addr raft.ErrProposalDropped) ↦□ err)) -∗
  step_post γ cfg r id (to_pstate s) m Φ -∗
  |={⊤}=> Φ #err.
Proof.
  iIntros (Hcfg Hwf' Hstep) "Hghost Hphys Herr HΦ".
  assert (Hst' : step γ.(re_cfg) id (to_pstate s) [] (to_pstate s'))
    by (rewrite Hcfg; exact Hstep).
  iMod (own_raft_ghost_step_0 _ _ _ _ Hst' with "Hghost") as "Hghost".
  iModIntro. iApply ("HΦ" $! err s' (to_pstate s')). iFrame.
  iPureIntro. split; [split; [done|exact Hwf']|]. by eexists [].
Qed.

(** The message's [Entries], read-only for every type but a proposal. *)
Lemma ents_ro (m : raftpb.Message.t) (ents : list raftpb.Entry.t) :
  m.(raftpb.Message.Type') ≠ MsgProp →
  (if decide (m.(raftpb.Message.Type') = MsgProp)
   then m.(raftpb.Message.Entries') ↦* ents
   else m.(raftpb.Message.Entries') ↦*□ ents) -∗
  m.(raftpb.Message.Entries') ↦*□ ents.
Proof. intros Hne. rewrite decide_False //. auto. Qed.

(** *** The dispatch for the branches written elsewhere

    Each takes the branch lemma, at the statement agreed for it, as the
    hypothesis [HB], and proves [Step]'s spec for that message type from
    it.  The statements are the branch lemmas' own (2026-10-02).  [MsgApp]
    and [MsgHeartbeat] also take [follower_votes_ok] ([protocol.v]), and
    one guard each (marked GUARD, also in the branch files): the protocol fact behind the conflict
    premise ([app_no_conflict_below_commit]) and the commit premise
    ([heartbeat_commit_le_last]) holds only for a message no older than the
    receiver's term -- a stale [MsgApp] from a deposed leader can conflict
    below the commit index -- and a stale message never reaches
    [maybeAppend]/[commitTo] ([Step]'s preamble drops it), so the branch
    lemma needs the premise only under [uint.Z s.term ≤ uint.Z m.Term]. *)

Lemma dispatch_App γ cfg r id s (m : raftpb.Message.t) (ents : list raftpb.Entry.t)
    (Φ : val → iProp Σ) :
  (m.(raftpb.Message.Type') = MsgApp →
   m.(raftpb.Message.To') = id →
   m.(raftpb.Message.Term') ≠ W64 0 →
   m.(raftpb.Message.From') ≠ W64 0 →
   m.(raftpb.Message.From') ≠ id →
   id ∈ cfg →
   nstate_wf s →
   plog_wf (raft.entryID.mk m.(raftpb.Message.LogTerm') m.(raftpb.Message.Index')) ents →
   (uint.Z m.(raftpb.Message.Index') + Z.of_nat (length ents) + 1 < 2^64)%Z →
   Forall (λ e, e.(raftpb.Entry.Type') = EntryNormal) ents →
   (let ls := s.(nstate.logst) in
    let es := ls.(logstate.sents) ++ ls.(logstate.uents) in
    uint.Z s.(nstate.term) ≤ uint.Z m.(raftpb.Message.Term') →   (* GUARD *)
    uint.Z ls.(logstate.committed) ≤ uint.Z m.(raftpb.Message.Index') →
    plog_matches ls.(logstate.prev) es
      (raft.entryID.mk m.(raftpb.Message.LogTerm') m.(raftpb.Message.Index')) →
    plog_find_conflict ls.(logstate.prev) es ents = W64 0 ∨
    uint.Z ls.(logstate.committed) < uint.Z (plog_find_conflict ls.(logstate.prev) es ents))%Z →
   (s.(nstate.role) = prole.Follower → s.(nstate.votes) = ∅) →
   {{{ is_pkg_init raft ∗ "Hphys" ∷ own_raft_phys cfg r id s ∗
       "#Hents" ∷ m.(raftpb.Message.Entries') ↦*□ ents ∗
       "Hcap" ∷ own_slice_cap raftpb.Entry.t m.(raftpb.Message.Entries') (DfracOwn 1) }}}
     r @! (go.PointerType raft.raft) @! "Step" #m
   {{{ (err : error.t) s', RET #err;
       "Hphys" ∷ own_raft_phys cfg r id s' ∗
       "%Hwf'" ∷ ⌜ nstate_wf s' ⌝ ∗
       "%Hrefines" ∷ ⌜ ∃ recv,
           (∀ m', m' ∈ recv → m' = abs_msg mtype.App m ents) ∧
           step cfg id (to_pstate s) recv (to_pstate s') ⌝ ∗
       "%Herr" ∷ ⌜ err = interface.nil ⌝ }}}) →
  γ.(re_cfg) = cfg →
  id ∈ cfg →
  nstate_wf s →
  m.(raftpb.Message.Type') = MsgApp →
  m.(raftpb.Message.To') = id ∧ m.(raftpb.Message.Term') ≠ W64 0 ∧
  m.(raftpb.Message.From') ≠ W64 0 ∧ m.(raftpb.Message.From') ≠ id →
  is_pkg_init raft -∗
  own_raft_phys cfg r id s -∗
  own_raft_ghost γ id (to_pstate s) -∗
  m.(raftpb.Message.Entries') ↦*□ ents -∗
  own_slice_cap raftpb.Entry.t m.(raftpb.Message.Entries') (DfracOwn 1) -∗
  is_message γ (abs_msg mtype.App m ents) -∗
  ▷ step_post γ cfg r id (to_pstate s) m Φ -∗
  WP r @! (go.PointerType raft.raft) @! "Step" #m {{ v, |={⊤}=> Φ v }}.
Proof.
  iIntros (HB Hcfg Hin Hwf Hty (Hto & Hterm & Hfnz & Hfid))
    "#Hinit Hphys Hghost #Hents Hcap #Hm HΦ".
  (* [maybeAppend]'s batch facts: carried by the message *)
  iDestruct (app_recv_wf with "Hghost Hm") as %(Hpwf & Hnw & Hnorm); [done|exact Hto|].
  (* the conflict fact: the protocol's, for a message no older than us *)
  iAssert (⌜ uint.Z s.(nstate.term) ≤ uint.Z m.(raftpb.Message.Term') →
             let ls := s.(nstate.logst) in
             let es := ls.(logstate.sents) ++ ls.(logstate.uents) in
             uint.Z ls.(logstate.committed) ≤ uint.Z m.(raftpb.Message.Index') →
             plog_matches ls.(logstate.prev) es
               (raft.entryID.mk m.(raftpb.Message.LogTerm') m.(raftpb.Message.Index')) →
             plog_find_conflict ls.(logstate.prev) es ents = W64 0 ∨
             uint.Z ls.(logstate.committed)
             < uint.Z (plog_find_conflict ls.(logstate.prev) es ents) ⌝ ∗
           own_raft_ghost γ id (to_pstate s))%I with "[Hghost]" as "[%Hconf Hghost]".
  { destruct (decide (uint.Z s.(nstate.term) ≤ uint.Z m.(raftpb.Message.Term') ∧
                      uint.Z s.(nstate.logst).(logstate.committed)
                      ≤ uint.Z m.(raftpb.Message.Index'))) as [[Hle Hcm]|Hn].
    - iDestruct (app_no_conflict_below_commit with "Hghost Hm") as %Hc;
        [done|exact Hto|exact Hle|exact Hcm|].
      iFrame "Hghost". iPureIntro. intros _ _. exact Hc.
    - iFrame "Hghost". iPureIntro. intros Hle Hcm. exfalso. by apply Hn. }
  (* a follower's tally is empty: the code's [r.lead = m.From] and the
     model's [padopt_leader] agree *)
  iDestruct (own_raft_ghost_follower_votes with "Hghost") as %Hfv0.
  pose proof (follower_votes_ok_phys s Hfv0) as Hfv.
  wp_apply (HB Hty Hto Hterm Hfnz Hfid Hin Hwf Hpwf Hnw Hnorm Hconf Hfv
             with "[$Hinit $Hphys $Hents $Hcap]").
  iIntros (err s') "(Hphys & %Hwf' & %Hst & %Herr)".
  destruct Hst as (recv & Hrecv & Hstep).
  iApply (finish_branch with "Hm Hghost Hphys [] HΦ"); [done..|].
  iLeft. by iPureIntro.
Qed.

Lemma dispatch_Heartbeat γ cfg r id s (m : raftpb.Message.t) (ents : list raftpb.Entry.t)
    (Φ : val → iProp Σ) :
  (m.(raftpb.Message.Type') = MsgHeartbeat →
   m.(raftpb.Message.To') = id →
   m.(raftpb.Message.Term') ≠ W64 0 →
   m.(raftpb.Message.From') ≠ W64 0 →
   m.(raftpb.Message.From') ≠ id →
   id ∈ cfg →
   nstate_wf s →
   (uint.Z s.(nstate.term) ≤ uint.Z m.(raftpb.Message.Term') →   (* GUARD *)
    uint.Z m.(raftpb.Message.Commit')
    ≤ plog_last_index_Z s.(nstate.logst).(logstate.prev)
        (s.(nstate.logst).(logstate.sents) ++ s.(nstate.logst).(logstate.uents)))%Z →
   (s.(nstate.role) = prole.Follower → s.(nstate.votes) = ∅) →
   {{{ is_pkg_init raft ∗ "Hphys" ∷ own_raft_phys cfg r id s ∗
       "#Hents" ∷ m.(raftpb.Message.Entries') ↦*□ ents }}}
     r @! (go.PointerType raft.raft) @! "Step" #m
   {{{ (err : error.t) s', RET #err;
       "Hphys" ∷ own_raft_phys cfg r id s' ∗
       "%Hwf'" ∷ ⌜ nstate_wf s' ⌝ ∗
       "%Hrefines" ∷ ⌜ ∃ recv,
           (∀ m', m' ∈ recv → m' = abs_msg mtype.Heartbeat m ents) ∧
           step cfg id (to_pstate s) recv (to_pstate s') ⌝ ∗
       "%Herr" ∷ ⌜ err = interface.nil ⌝ }}}) →
  γ.(re_cfg) = cfg →
  id ∈ cfg →
  nstate_wf s →
  m.(raftpb.Message.Type') = MsgHeartbeat →
  m.(raftpb.Message.To') = id ∧ m.(raftpb.Message.Term') ≠ W64 0 ∧
  m.(raftpb.Message.From') ≠ W64 0 ∧ m.(raftpb.Message.From') ≠ id →
  is_pkg_init raft -∗
  own_raft_phys cfg r id s -∗
  own_raft_ghost γ id (to_pstate s) -∗
  m.(raftpb.Message.Entries') ↦*□ ents -∗
  is_message γ (abs_msg mtype.Heartbeat m ents) -∗
  ▷ step_post γ cfg r id (to_pstate s) m Φ -∗
  WP r @! (go.PointerType raft.raft) @! "Step" #m {{ v, |={⊤}=> Φ v }}.
Proof.
  iIntros (HB Hcfg Hin Hwf Hty (Hto & Hterm & Hfnz & Hfid))
    "#Hinit Hphys Hghost #Hents #Hm HΦ".
  iAssert (⌜ uint.Z s.(nstate.term) ≤ uint.Z m.(raftpb.Message.Term') →
             uint.Z m.(raftpb.Message.Commit')
             ≤ plog_last_index_Z s.(nstate.logst).(logstate.prev)
                 (s.(nstate.logst).(logstate.sents) ++ s.(nstate.logst).(logstate.uents)) ⌝ ∗
           own_raft_ghost γ id (to_pstate s))%I with "[Hghost]" as "[%Hcl Hghost]".
  { destruct (decide (uint.Z s.(nstate.term) ≤ uint.Z m.(raftpb.Message.Term')))
      as [Hle|Hle]; last first.
    { iFrame "Hghost". iPureIntro. intros ?. lia. }
    destruct (decide (m.(raftpb.Message.Term') = s.(nstate.term) ∧
                      s.(nstate.role) = prole.Leader)) as [[Heq Hr]|Hnl].
    - (* a leader receiving a heartbeat of its own term: the sender is a
         second leader of the term, which [is_leader_unique] excludes *)
      iDestruct (own_raft_ghost_is_leader with "Hghost") as "#Hl1";
        first (rewrite to_pstate_role Hr //).
      iPoseProof "Hm" as "Hm2". iEval (rewrite /is_message /=) in "Hm2".
      iDestruct "Hm2" as "[Hl2 _]".
      iEval (rewrite Heq) in "Hl2".
      iDestruct (is_leader_unique with "Hl1 Hl2") as %Hid.
      exfalso. apply Hfid. by rewrite Hid.
    - iDestruct (heartbeat_commit_le_last with "Hghost Hm") as %Hc;
        [done|exact Hto|exact Hle| |].
      { intros Heq Hr. apply Hnl. split; [exact Heq|by apply prole_role_leader]. }
      iFrame "Hghost". iPureIntro. intros _. exact Hc. }
  iDestruct (own_raft_ghost_follower_votes with "Hghost") as %Hfv0.
  pose proof (follower_votes_ok_phys s Hfv0) as Hfv.
  wp_apply (HB Hty Hto Hterm Hfnz Hfid Hin Hwf Hcl Hfv with "[$Hinit $Hphys $Hents]").
  iIntros (err s') "(Hphys & %Hwf' & %Hst & %Herr)".
  destruct Hst as (recv & Hrecv & Hstep).
  iApply (finish_branch with "Hm Hghost Hphys [] HΦ"); [done..|].
  iLeft. by iPureIntro.
Qed.

Lemma dispatch_AppResp γ cfg r id s (m : raftpb.Message.t) (ents : list raftpb.Entry.t)
    (Φ : val → iProp Σ) :
  (m.(raftpb.Message.Type') = MsgAppResp →
   m.(raftpb.Message.To') = id →
   m.(raftpb.Message.Term') ≠ W64 0 →
   m.(raftpb.Message.From') ≠ W64 0 →
   (m.(raftpb.Message.Reject') = true → m.(raftpb.Message.From') ≠ id) →
   id ∈ cfg →
   nstate_wf s →
   {{{ is_pkg_init raft ∗ "Hphys" ∷ own_raft_phys cfg r id s ∗
       "#Hents" ∷ m.(raftpb.Message.Entries') ↦*□ ents }}}
     r @! (go.PointerType raft.raft) @! "Step" #m
   {{{ (err : error.t) s', RET #err;
       "Hphys" ∷ own_raft_phys cfg r id s' ∗
       "%Hwf'" ∷ ⌜ nstate_wf s' ⌝ ∗
       "%Hrefines" ∷ ⌜ ∃ recv,
           (∀ m', m' ∈ recv → m' = abs_msg mtype.AppResp m ents) ∧
           step cfg id (to_pstate s) recv (to_pstate s') ⌝ ∗
       "%Herr" ∷ ⌜ err = interface.nil ⌝ }}}) →
  γ.(re_cfg) = cfg →
  id ∈ cfg →
  nstate_wf s →
  m.(raftpb.Message.Type') = MsgAppResp →
  m.(raftpb.Message.To') = id ∧ m.(raftpb.Message.Term') ≠ W64 0 ∧
  m.(raftpb.Message.From') ≠ W64 0 ∧
  (m.(raftpb.Message.Reject') = true → m.(raftpb.Message.From') ≠ id) →
  is_pkg_init raft -∗
  own_raft_phys cfg r id s -∗
  own_raft_ghost γ id (to_pstate s) -∗
  m.(raftpb.Message.Entries') ↦*□ ents -∗
  is_message γ (abs_msg mtype.AppResp m ents) -∗
  ▷ step_post γ cfg r id (to_pstate s) m Φ -∗
  WP r @! (go.PointerType raft.raft) @! "Step" #m {{ v, |={⊤}=> Φ v }}.
Proof.
  iIntros (HB Hcfg Hin Hwf Hty (Hto & Hterm & Hfnz & Hrej))
    "#Hinit Hphys Hghost #Hents #Hm HΦ".
  wp_apply (HB Hty Hto Hterm Hfnz Hrej Hin Hwf with "[$Hinit $Hphys $Hents]").
  iIntros (err s') "(Hphys & %Hwf' & %Hst & %Herr)".
  destruct Hst as (recv & Hrecv & Hstep).
  iApply (finish_branch with "Hm Hghost Hphys [] HΦ"); [done..|].
  iLeft. by iPureIntro.
Qed.

Lemma dispatch_HeartbeatResp γ cfg r id s (m : raftpb.Message.t) (ents : list raftpb.Entry.t)
    (Φ : val → iProp Σ) :
  (m.(raftpb.Message.Type') = MsgHeartbeatResp →
   m.(raftpb.Message.To') = id →
   m.(raftpb.Message.Term') ≠ W64 0 →
   m.(raftpb.Message.From') ≠ W64 0 →
   m.(raftpb.Message.From') ≠ id →
   id ∈ cfg →
   nstate_wf s →
   {{{ is_pkg_init raft ∗ "Hphys" ∷ own_raft_phys cfg r id s ∗
       "#Hents" ∷ m.(raftpb.Message.Entries') ↦*□ ents ∗
       "#Hctx0" ∷ m.(raftpb.Message.Context') ↦*□ ([] : list w8) }}}
     r @! (go.PointerType raft.raft) @! "Step" #m
   {{{ (err : error.t) s', RET #err;
       "Hphys" ∷ own_raft_phys cfg r id s' ∗
       "%Hwf'" ∷ ⌜ nstate_wf s' ⌝ ∗
       "%Hrefines" ∷ ⌜ ∃ recv,
           (∀ m', m' ∈ recv → m' = abs_msg mtype.HeartbeatResp m ents) ∧
           step cfg id (to_pstate s) recv (to_pstate s') ⌝ ∗
       "%Herr" ∷ ⌜ err = interface.nil ⌝ }}}) →
  γ.(re_cfg) = cfg →
  id ∈ cfg →
  nstate_wf s →
  m.(raftpb.Message.Type') = MsgHeartbeatResp →
  m.(raftpb.Message.To') = id ∧ m.(raftpb.Message.Term') ≠ W64 0 ∧
  m.(raftpb.Message.From') ≠ W64 0 ∧ m.(raftpb.Message.From') ≠ id →
  is_pkg_init raft -∗
  own_raft_phys cfg r id s -∗
  own_raft_ghost γ id (to_pstate s) -∗
  m.(raftpb.Message.Entries') ↦*□ ents -∗
  m.(raftpb.Message.Context') ↦*□ ([] : list w8) -∗
  is_message γ (abs_msg mtype.HeartbeatResp m ents) -∗
  ▷ step_post γ cfg r id (to_pstate s) m Φ -∗
  WP r @! (go.PointerType raft.raft) @! "Step" #m {{ v, |={⊤}=> Φ v }}.
Proof.
  iIntros (HB Hcfg Hin Hwf Hty (Hto & Hterm & Hfnz & Hfid))
    "#Hinit Hphys Hghost #Hents #Hctx0 #Hm HΦ".
  wp_apply (HB Hty Hto Hterm Hfnz Hfid Hin Hwf with "[$Hinit $Hphys $Hents $Hctx0]").
  iIntros (err s') "(Hphys & %Hwf' & %Hst & %Herr)".
  destruct Hst as (recv & Hrecv & Hstep).
  iApply (finish_branch with "Hm Hghost Hphys [] HΦ"); [done..|].
  iLeft. by iPureIntro.
Qed.

Lemma dispatch_Beat γ cfg r id s (m : raftpb.Message.t) (Φ : val → iProp Σ) :
  (m.(raftpb.Message.Type') = MsgBeat →
   m.(raftpb.Message.Term') = W64 0 →
   id ∈ cfg →
   nstate_wf s →
   {{{ is_pkg_init raft ∗ "Hphys" ∷ own_raft_phys cfg r id s }}}
     r @! (go.PointerType raft.raft) @! "Step" #m
   {{{ (err : error.t) s', RET #err;
       "Hphys" ∷ own_raft_phys cfg r id s' ∗
       "%Hwf'" ∷ ⌜ nstate_wf s' ⌝ ∗
       "%Hrefines" ∷ ⌜ step cfg id (to_pstate s) [] (to_pstate s') ⌝ ∗
       "%Herr" ∷ ⌜ err = interface.nil ⌝ }}}) →
  γ.(re_cfg) = cfg →
  id ∈ cfg →
  nstate_wf s →
  m.(raftpb.Message.Type') = MsgBeat →
  m.(raftpb.Message.Term') = W64 0 →
  is_pkg_init raft -∗
  own_raft_phys cfg r id s -∗
  own_raft_ghost γ id (to_pstate s) -∗
  ▷ step_post γ cfg r id (to_pstate s) m Φ -∗
  WP r @! (go.PointerType raft.raft) @! "Step" #m {{ v, |={⊤}=> Φ v }}.
Proof.
  iIntros (HB Hcfg Hin Hwf Hty Hterm) "#Hinit Hphys Hghost HΦ".
  wp_apply (HB Hty Hterm Hin Hwf with "[$Hinit $Hphys]").
  iIntros (err s') "(Hphys & %Hwf' & %Hst & %Herr)".
  iApply (finish_branch0 with "Hghost Hphys [] HΦ"); [done..|].
  iLeft. by iPureIntro.
Qed.

(** [MsgSnap] (2026-10-02): the snapshot and its voters come from
    ["Hsnap"].  At the current term the receiver is not a leader -- the
    sender leads that term ([is_message]'s [is_leader], [is_leader_unique])
    -- and a follower's tally is empty ([follower_votes_ok]); the three
    [step_snap_*] rules need no other protocol fact: a restore replaces the
    log wholesale and the fast-forward's [commitTo] is in range by
    [matchTerm]. *)
Lemma dispatch_Snap γ cfg r id s (m : raftpb.Message.t)
    (sv : raftpb.Snapshot.t) (voters : list w64) (Φ : val → iProp Σ) :
  (m.(raftpb.Message.Type') = MsgSnap →
   m.(raftpb.Message.To') = id →
   m.(raftpb.Message.Term') ≠ W64 0 →
   m.(raftpb.Message.From') ≠ W64 0 →
   m.(raftpb.Message.From') ≠ id →
   id ∈ cfg →
   nstate_wf s →
   snap_scope cfg sv voters →
   (m.(raftpb.Message.Term') = s.(nstate.term) → s.(nstate.role) ≠ prole.Leader) →
   (s.(nstate.role) = prole.Follower → s.(nstate.votes) = ∅) →
   {{{ is_pkg_init raft ∗ "Hphys" ∷ own_raft_phys cfg r id s ∗
       "#Hsv" ∷ m.(raftpb.Message.Snapshot') ↦□ sv ∗
       "#Hvs" ∷ sv.(raftpb.Snapshot.Metadata').(raftpb.SnapshotMetadata.ConfState')
                  .(raftpb.ConfState.Voters') ↦*□ voters }}}
     r @! (go.PointerType raft.raft) @! "Step" #m
   {{{ (err : error.t) s', RET #err;
       "Hphys" ∷ own_raft_phys cfg r id s' ∗
       "%Hwf'" ∷ ⌜ nstate_wf s' ⌝ ∗
       "%Hrefines" ∷ ⌜ ∃ recv,
           (∀ m', m' ∈ recv → m' = abs_snap m sv voters) ∧
           step cfg id (to_pstate s) recv (to_pstate s') ⌝ ∗
       "%Herr" ∷ ⌜ err = interface.nil ⌝ }}}) →
  γ.(re_cfg) = cfg →
  id ∈ cfg →
  nstate_wf s →
  m.(raftpb.Message.Type') = MsgSnap →
  m.(raftpb.Message.To') = id ∧ m.(raftpb.Message.Term') ≠ W64 0 ∧
  m.(raftpb.Message.From') ≠ W64 0 ∧ m.(raftpb.Message.From') ≠ id →
  snap_scope cfg sv voters →
  is_pkg_init raft -∗
  own_raft_phys cfg r id s -∗
  own_raft_ghost γ id (to_pstate s) -∗
  m.(raftpb.Message.Snapshot') ↦□ sv -∗
  sv.(raftpb.Snapshot.Metadata').(raftpb.SnapshotMetadata.ConfState')
    .(raftpb.ConfState.Voters') ↦*□ voters -∗
  is_message γ (abs_snap m sv voters) -∗
  ▷ step_post γ cfg r id (to_pstate s) m Φ -∗
  WP r @! (go.PointerType raft.raft) @! "Step" #m {{ v, |={⊤}=> Φ v }}.
Proof.
  iIntros (HB Hcfg Hin Hwf Hty (Hto & Hterm & Hfnz & Hfid) Hscope)
    "#Hinit Hphys Hghost #Hsv #Hvs #Hm HΦ".
  (* at the current term the receiver is not a leader: the sender leads it *)
  iAssert (⌜ m.(raftpb.Message.Term') = s.(nstate.term) →
             s.(nstate.role) ≠ prole.Leader ⌝ ∗
           own_raft_ghost γ id (to_pstate s))%I with "[Hghost]" as "[%Hnl Hghost]".
  { destruct (decide (m.(raftpb.Message.Term') = s.(nstate.term) ∧
                      s.(nstate.role) = prole.Leader)) as [[Heq Hr]|Hn].
    - iDestruct (own_raft_ghost_is_leader with "Hghost") as "#Hl1";
        first (rewrite to_pstate_role Hr //).
      iPoseProof "Hm" as "Hm2". iEval (rewrite /is_message /=) in "Hm2".
      iDestruct "Hm2" as "[Hl2 _]".
      iEval (rewrite Heq) in "Hl2".
      iDestruct (is_leader_unique with "Hl1 Hl2") as %Hid.
      exfalso. apply Hfid. by rewrite Hid.
    - iFrame "Hghost". iPureIntro. intros Heq Hr. apply Hn. split; [exact Heq|exact Hr]. }
  iDestruct (own_raft_ghost_follower_votes with "Hghost") as %Hfv0.
  pose proof (follower_votes_ok_phys s Hfv0) as Hfv.
  wp_apply (HB Hty Hto Hterm Hfnz Hfid Hin Hwf Hscope Hnl Hfv
             with "[$Hinit $Hphys $Hsv $Hvs]").
  iIntros (err s') "(Hphys & %Hwf' & %Hst & %Herr)".
  destruct Hst as (recv & Hrecv & Hstep).
  iApply (finish_branch with "Hm Hghost Hphys [] HΦ"); [done..|].
  iLeft. by iPureIntro.
Qed.

End dispatch.

(** [wp_raft__Step]'s type is closed, so the prelude default is what the
    proof should use (the branch files set [Default Proof Using "W"] inside
    their sections; that setting does not cross a [Require]). *)
Set Default Proof Using "Type".


  (** The top-level dispatch: the one triple in [STEP], and **the one place in
      this development where ghost state is updated**.  Each branch lemma
      hands back a pure [step] witness together with the list of messages it
      consumed; here that becomes a single [own_raft_ghost_step].

      [iApply wp_fupd] up front is what makes that possible: the ghost update
      has to happen after the branch lemma returns, when the goal would
      otherwise be the bare postcondition with no fancy update to absorb.

      The type is decided one candidate at a time, in [step_msg_types]'s
      order; what is left is none of them, which [step_msg] excludes. *)
  Lemma wp_raft__Step : wp_raft__Step_body.
  Proof.
    intros_ambient.
    intros cfg γ r id s ps m.
    (* Not [subst cfg]: the branch lemmas below are applied to [cfg] by
       name, and with the binder gone that resolves to Perennial's global
       [cfg] (a [language → Type]).  Move the witness instead. *)
    intros Hcfg.
    intros Hsm Hin Hhup Hvote Hvoteresp Hprevote Hprevoteresp Happ Hhb Happresp Hhbresp
      Hsnapt Hbeat Hprop Hrel.
    destruct Hrel as [<- Hwf].
    iIntros (Φ) "(#Hinit & Hphys & Hghost & Hm & #Hctx & #Hsnap) HΦ".
    iDestruct "Hm" as (ents) "(Hents & Hcap & %Hpents & #Hmsg0)".
    iApply wp_fupd.
    destruct (decide (m.(raftpb.Message.Type') = MsgSnap)) as [Hty|Hns].
    { (* MsgSnap: [dispatch_Snap], with the snapshot from ["Hsnap"]. *)
      iDestruct ("Hsnap" with "[//]") as (sv voters) "(#Hsv & #Hvs & %Hscope & #Hm')".
      iApply (dispatch_Snap with "Hinit Hphys Hghost Hsv Hvs Hm' HΦ");
        [exact (SN.wp_Step_MsgSnap cfg r id s m sv voters)|done..|exact (Hsnapt Hty)|exact Hscope]. }
    (* from here on [m] is not a [MsgSnap], so [Hm]'s [ty ≠ Snap] guard
       always holds *)
    iAssert (□ ∀ ty, ⌜ mtype_of m.(raftpb.Message.Type') = Some ty ⌝ -∗
                     is_message γ (abs_msg ty m ents))%I as "#Hmsg".
    { iIntros "!> %ty %Hty". iApply ("Hmsg0" with "[//] [%]").
      intros ->. exact (Hns (mtype_of_Snap _ Hty)). }
    iClear "Hsnap Hmsg0".
    destruct (decide (m.(raftpb.Message.Type') = MsgHup)) as [Hty|Hn_hup].
    { (* MsgHup: a local message, handled by [hup]. *)
      destruct (Hhup Hty) as [Hmterm Hnowrap].
      wp_apply (H.wp_Step_MsgHup cfg with "[$Hphys]"); [done..|].
      iIntros (err s') "(Hphys & %Hwf' & %Hst & %Herr)".
      iApply (finish_branch0 with "Hghost Hphys [] HΦ"); [done..|].
      iLeft. by iPureIntro. }
    destruct (decide (m.(raftpb.Message.Type') = MsgVote)) as [Hty|Hn_vote].
    { (* MsgVote: answer the vote request, stepping down first if needed. *)
      destruct (Hvote Hty) as (Hto & Hterm & Hfnz).
      iDestruct ("Hmsg" $! mtype.Vote with "[]") as "#Hm'".
      { iPureIntro. rewrite Hty. apply mtype_of_MsgVote. }
      iAssert (∃ ctx, m.(raftpb.Message.Context') ↦*□ ctx ∗
                      ⌜ ctx ≠ campaignTransfer ⌝)%I as "#Hctx'".
      { iDestruct "Hctx" as (ctx) "(#Hc & %Hc2 & _)".
        iExists ctx. iFrame "Hc". iPureIntro. exact Hc2. }
      wp_apply (V.wp_Step_MsgVote cfg _ _ _ _ ents with "[$Hphys $Hctx']"); [done..|].
      iIntros (err s') "(Hphys & %Hwf' & %Hst & %Herr)".
      destruct Hst as (recv & Hrecv & Hstep).
      iApply (finish_branch with "Hm' Hghost Hphys [] HΦ"); [done..|].
      iLeft. by iPureIntro. }
    destruct (decide (m.(raftpb.Message.Type') = MsgVoteResp)) as [Hty|Hn_vr].
    { (* MsgVoteResp: tally the vote, possibly winning or losing. *)
      destruct (Hvoteresp Hty) as [Hto Hterm].
      iDestruct ("Hmsg" $! mtype.VoteResp with "[]") as "#Hm'".
      { iPureIntro. rewrite Hty. apply mtype_of_MsgVoteResp. }
      wp_apply (R.wp_Step_MsgVoteResp cfg _ _ _ _ ents with "[$Hphys]"); [done..|].
      iIntros (err s') "(Hphys & %Hwf' & %Hst & %Herr)".
      destruct Hst as (recv & Hrecv & Hstep).
      iApply (finish_branch with "Hm' Hghost Hphys [] HΦ"); [done..|].
      iLeft. by iPureIntro. }
    destruct (decide (m.(raftpb.Message.Type') = MsgPreVote)) as [Hty|Hn_pv].
    { (* MsgPreVote (2026-10-04): answered with a free [MsgPreVoteResp];
         nothing received, nothing recorded. *)
      destruct (Hprevote Hty) as (Hto & Hterm & Hfnz & _ & Hutd0).
      iAssert (∃ ctx, m.(raftpb.Message.Context') ↦*□ ctx ∗
                      ⌜ ctx ≠ campaignTransfer ⌝)%I as "#Hctx'".
      { iDestruct "Hctx" as (ctx) "(#Hc & %Hc2 & _)".
        iExists ctx. iFrame "Hc". iPureIntro. exact Hc2. }
      wp_apply (PV.wp_Step_MsgPreVote cfg with "[$Hphys $Hctx']"); [done..|].
      iIntros (err s') "(Hphys & %Hwf' & %Hst & %Herr)".
      iApply (finish_branch0 with "Hghost Hphys [] HΦ"); [done..|].
      iLeft. by iPureIntro. }
    destruct (decide (m.(raftpb.Message.Type') = MsgPreVoteResp)) as [Hty|Hn_pvr].
    { (* MsgPreVoteResp (2026-10-04): a pre-candidate's tally, or a
         step-down on a rejection of a higher term. *)
      destruct (Hprevoteresp Hty) as (Hto & Hterm & _ & Hnw).
      iDestruct ("Hmsg" $! mtype.PreVoteResp with "[]") as "#Hm'".
      { iPureIntro. rewrite Hty. apply mtype_of_MsgPreVoteResp. }
      wp_apply (PR.wp_Step_MsgPreVoteResp cfg _ _ _ _ ents with "[$Hphys]"); [done..|].
      iIntros (err s') "(Hphys & %Hwf' & %Hst & %Herr)".
      destruct Hst as (recv & Hrecv & Hstep).
      iApply (finish_branch with "Hm' Hghost Hphys [] HΦ"); [done..|].
      iLeft. by iPureIntro. }
    destruct (decide (m.(raftpb.Message.Type') = MsgApp)) as [Hty|Hn_app].
    { (* MsgApp: [dispatch_App]. *)
      iDestruct ("Hmsg" $! mtype.App with "[]") as "#Hm'".
      { iPureIntro. rewrite Hty. apply mtype_of_MsgApp. }
      iDestruct (ents_ro with "Hents") as "#Hro"; first (rewrite Hty; w32_ne).
      iApply (dispatch_App with "Hinit Hphys Hghost Hro Hcap Hm' HΦ");
        [exact (A.wp_Step_MsgApp cfg r id s m ents)|done..|exact (Happ Hty)]. }
    destruct (decide (m.(raftpb.Message.Type') = MsgAppResp)) as [Hty|Hn_ar].
    { (* MsgAppResp: [dispatch_AppResp]. *)
      iDestruct ("Hmsg" $! mtype.AppResp with "[]") as "#Hm'".
      { iPureIntro. rewrite Hty. apply mtype_of_MsgAppResp. }
      iDestruct (ents_ro with "Hents") as "#Hro"; first (rewrite Hty; w32_ne).
      iApply (dispatch_AppResp with "Hinit Hphys Hghost Hro Hm' HΦ");
        [exact (AR.wp_Step_MsgAppResp cfg r id s m ents)|done..|exact (Happresp Hty)]. }
    destruct (decide (m.(raftpb.Message.Type') = MsgHeartbeat)) as [Hty|Hn_hb].
    { (* MsgHeartbeat: [dispatch_Heartbeat]. *)
      iDestruct ("Hmsg" $! mtype.Heartbeat with "[]") as "#Hm'".
      { iPureIntro. rewrite Hty. apply mtype_of_MsgHeartbeat. }
      iDestruct (ents_ro with "Hents") as "#Hro"; first (rewrite Hty; w32_ne).
      iApply (dispatch_Heartbeat with "Hinit Hphys Hghost Hro Hm' HΦ");
        [exact (HB.wp_Step_MsgHeartbeat cfg r id s m ents)|done..|exact (Hhb Hty)]. }
    destruct (decide (m.(raftpb.Message.Type') = MsgHeartbeatResp)) as [Hty|Hn_hr].
    { (* MsgHeartbeatResp: [dispatch_HeartbeatResp]; the [Context] is empty. *)
      iDestruct ("Hmsg" $! mtype.HeartbeatResp with "[]") as "#Hm'".
      { iPureIntro. rewrite Hty. apply mtype_of_MsgHeartbeatResp. }
      iDestruct (ents_ro with "Hents") as "#Hro"; first (rewrite Hty; w32_ne).
      iDestruct "Hctx" as (ctx) "(#Hctxp & _ & %Hctx0)".
      rewrite (Hctx0 Hty).
      iApply (dispatch_HeartbeatResp with "Hinit Hphys Hghost Hro Hctxp Hm' HΦ");
        [exact (HR.wp_Step_MsgHeartbeatResp cfg r id s m ents)|done..|exact (Hhbresp Hty)]. }
    destruct (decide (m.(raftpb.Message.Type') = MsgBeat)) as [Hty|Hn_beat].
    { (* MsgBeat: [dispatch_Beat]. *)
      iApply (dispatch_Beat with "Hinit Hphys Hghost HΦ");
        [exact (B.wp_Step_MsgBeat cfg r id s m)|done..|exact (Hbeat Hty)]. }
    destruct (decide (m.(raftpb.Message.Type') = MsgProp)) as [Hty|Hn_prop].
    { (* MsgProp: forward, append or drop ([proof_raft__Step_MsgProp.v]).
         The node's own [lead_ok] is what the follower's forwarding needs. *)
      destruct (Hprop Hty) as [Hterm Hfrom].
      destruct (Hpents Hty) as (Hne & Hnorm & Hlen).
      iDestruct (own_raft_ghost_lead_ok with "Hghost") as %Hlok0.
      (* a follower's leader is its physical one *)
      assert (Hlok : s.(nstate.role) = prole.Follower → s.(nstate.lead) ≠ id).
      { intros Hf. rewrite -(to_pstate_lead_nonpre s); last (rewrite Hf; discriminate).
        apply Hlok0. rewrite to_pstate_role Hf. discriminate. }
      iDestruct ("Hmsg" $! mtype.Propose with "[]") as "#Hm'".
      { iPureIntro. rewrite Hty. apply mtype_of_MsgProp. }
      (* [Hents] is owned: the [destruct (decide …)] above reduced its
         [if decide (Type = MsgProp)] *)
      wp_apply (M.wp_Step_MsgProp cfg r id s m ents Hty Hterm Hfrom Hne Hnorm Hlen Hlok Hin Hwf
                 with "[$Hinit $Hphys $Hents $Hcap]").
      iIntros (err s') "(Hphys & %Hwf' & %Hst & Herr)".
      destruct Hst as (recv & Hrecv & Hstep).
      iApply (finish_branch with "Hm' Hghost Hphys [Herr] HΦ"); [done..|].
      iDestruct "Herr" as "[%Herr|#Hd]"; [iLeft; by iPureIntro|iRight; by iFrame "#"]. }
    (* none of the twelve *)
    exfalso. cbv [step_msg step_msg_types] in Hsm.
    repeat (apply elem_of_cons in Hsm as [Hsm|Hsm]; [congruence|]).
    by apply elem_of_nil in Hsm.
  Qed.

End StepProof.

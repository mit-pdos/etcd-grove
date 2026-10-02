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
    [proof_raft__Step_MsgProp.v].  The branches for [MsgApp],
    [MsgHeartbeat], [MsgAppResp], [MsgHeartbeatResp] and [MsgBeat] are
    written in other branches of the work; their statements are fixed in
    advance, and this file's dispatch for each of them is a lemma
    ([dispatch_App], ...) that takes the branch lemma, at that statement, as
    a hypothesis.  So the ghost-side work -- deriving each branch's protocol
    premises from [own_raft_ghost] and [is_message], and taking
    [own_raft_ghost_step] with the branch's [recv] -- is checked now, and
    enabling a branch is a matter of applying its dispatch lemma to the
    branch lemma.  Until then [step_msg] ([spec_raft__Step.v]) is
    restricted to the four types whose branches exist.

    TO ENABLE the five branches, once their files are merged:
    1. [spec_raft__Step.v]: [step_msg_types := step_msg_all] (one line);
    2. below: uncomment the five [Require Export]s and the five
       [Module ... := ... P.] lines (marked "TO ENABLE");
    3. in [wp_raft__Step]: replace each [out_of_scope] line (marked
       "TO ENABLE") by the commented [iApply (dispatch_… …)] beside it. *)

Require Export New.proof.go_etcd_io.raft.election_proof.proof_raft__Step_helpers.proof_raft__Step_MsgHup.
Require Export New.proof.go_etcd_io.raft.election_proof.proof_raft__Step_helpers.proof_raft__Step_MsgVote.
Require Export New.proof.go_etcd_io.raft.election_proof.proof_raft__Step_helpers.proof_raft__Step_MsgVoteResp.
Require Export New.proof.go_etcd_io.raft.election_proof.proof_raft__Step_helpers.proof_raft__Step_MsgProp.
(* TO ENABLE:
Require Export New.proof.go_etcd_io.raft.election_proof.proof_raft__Step_helpers.proof_raft__Step_MsgApp.
Require Export New.proof.go_etcd_io.raft.election_proof.proof_raft__Step_helpers.proof_raft__Step_MsgHeartbeat.
Require Export New.proof.go_etcd_io.raft.election_proof.proof_raft__Step_helpers.proof_raft__Step_MsgAppResp.
Require Export New.proof.go_etcd_io.raft.election_proof.proof_raft__Step_helpers.proof_raft__Step_MsgHeartbeatResp.
Require Export New.proof.go_etcd_io.raft.election_proof.proof_raft__Step_helpers.proof_raft__Step_MsgBeat.
*)

Module StepProof (P : STEP_POSTULATES) : STEP.

Module H := StepMsgHup P.
Module V := StepMsgVote P.
Module R := StepMsgVoteResp P.
Module M := StepMsgProp P.
(* TO ENABLE:
Module A := StepMsgApp P.
Module HB := StepMsgHeartbeat P.
Module AR := StepMsgAppResp P.
Module HR := StepMsgHeartbeatResp P.
Module B := StepMsgBeat P.
*)

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
  rewrite -Hcfg in Hstep.
  iMod (own_raft_ghost_step_0 _ _ _ _ Hstep with "Hghost") as "Hghost".
  iModIntro. iApply ("HΦ" $! err s' (to_pstate s')). iFrame.
  iPureIntro. split; [split; [done|exact Hwf']|]. by eexists [].
Qed.

(** The message's [Entries], read-only for every type but a proposal, and
    owned for a proposal. *)
Lemma ents_ro (m : raftpb.Message.t) (ents : list raftpb.Entry.t) :
  m.(raftpb.Message.Type') ≠ MsgProp →
  (if decide (m.(raftpb.Message.Type') = MsgProp)
   then m.(raftpb.Message.Entries') ↦* ents
   else m.(raftpb.Message.Entries') ↦*□ ents) -∗
  m.(raftpb.Message.Entries') ↦*□ ents.
Proof. intros Hne. rewrite decide_False //. auto. Qed.

Lemma ents_own (m : raftpb.Message.t) (ents : list raftpb.Entry.t) :
  m.(raftpb.Message.Type') = MsgProp →
  (if decide (m.(raftpb.Message.Type') = MsgProp)
   then m.(raftpb.Message.Entries') ↦* ents
   else m.(raftpb.Message.Entries') ↦*□ ents) -∗
  m.(raftpb.Message.Entries') ↦* ents.
Proof. intros Heq. rewrite decide_True //. auto. Qed.

(** A type [step_msg] rules out. *)
Lemma not_step_msg (t : w32) :
  bool_decide (t ∈ step_msg_types) = false → t ∉ step_msg_types.
Proof. intros H. by apply bool_decide_eq_false_1 in H. Qed.

(** *** The dispatch for the branches written elsewhere

    Each takes the branch lemma, at the statement agreed for it, as the
    hypothesis [HB], and proves [Step]'s spec for that message type from
    it.  The statements are copied verbatim from the briefs of the branch
    work (2026-10-02) **except** for one guard each in [MsgApp] and
    [MsgHeartbeat] (marked GUARD): the protocol fact behind the conflict
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
  wp_apply (HB Hty Hto Hterm Hfnz Hfid Hin Hwf Hpwf Hnw Hnorm Hconf
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
                      s.(nstate.role) = role.Leader)) as [[Heq Hr]|Hnl].
    - (* a leader receiving a heartbeat of its own term: the sender is a
         second leader of the term, which [is_leader_unique] excludes *)
      iDestruct (own_raft_ghost_is_leader with "Hghost") as "#Hl1"; first exact Hr.
      iPoseProof "Hm" as "Hm2". iEval (rewrite /is_message /=) in "Hm2".
      iDestruct "Hm2" as "[Hl2 _]".
      iEval (rewrite Heq) in "Hl2".
      iDestruct (is_leader_unique with "Hl1 Hl2") as %Hid.
      exfalso. apply Hfid. by rewrite Hid.
    - iDestruct (heartbeat_commit_le_last with "Hghost Hm") as %Hc;
        [done|exact Hto|exact Hle| |].
      { intros Heq Hr. apply Hnl. split; [exact Heq|exact Hr]. }
      iFrame "Hghost". iPureIntro. intros _. exact Hc. }
  wp_apply (HB Hty Hto Hterm Hfnz Hfid Hin Hwf Hcl with "[$Hinit $Hphys $Hents]").
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

End dispatch.

(** [wp_raft__Step]'s type is closed, so the prelude default is what the
    proof should use (the branch files set [Default Proof Using "W"] inside
    their sections; that setting does not cross a [Require]). *)
Set Default Proof Using "Type".

(** A type outside [step_msg_types]: refuted by computing the membership. *)
Local Ltac out_of_scope Hsm Hty :=
  exfalso; revert Hsm; rewrite /step_msg Hty; apply not_step_msg; vm_compute; reflexivity.

  (** The top-level dispatch: the one triple in [STEP], and **the one place in
      this development where ghost state is updated**.  Each branch lemma
      hands back a pure [step] witness together with the list of messages it
      consumed; here that becomes a single [own_raft_ghost_step].

      [iApply wp_fupd] up front is what makes that possible: the ghost update
      has to happen after the branch lemma returns, when the goal would
      otherwise be the bare postcondition with no fancy update to absorb.

      The type is decided one candidate at a time, in [step_msg_all]'s
      order; what is left is none of them, which [step_msg] excludes. *)
  Lemma wp_raft__Step : wp_raft__Step_body.
  Proof.
    intros_ambient.
    intros cfg γ r id s ps m.
    (* Not [subst cfg]: the branch lemmas below are applied to [cfg] by
       name, and with the binder gone that resolves to Perennial's global
       [cfg] (a [language → Type]).  Move the witness instead. *)
    intros Hcfg.
    intros Hsm Hin Hhup Hvote Hvoteresp Happ Hhb Happresp Hhbresp Hbeat Hprop Hrel.
    destruct Hrel as [<- Hwf].
    iIntros (Φ) "(#Hinit & Hphys & Hghost & Hm & #Hctx) HΦ".
    iDestruct "Hm" as (ents) "(Hents & Hcap & %Hpents & #Hmsg)".
    iApply wp_fupd.
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
    destruct (decide (m.(raftpb.Message.Type') = MsgApp)) as [Hty|Hn_app].
    { (* MsgApp: [dispatch_App]. *)
      (* TO ENABLE: replace the next line by
      iDestruct ("Hmsg" $! mtype.App with "[]") as "#Hm'".
      { iPureIntro. rewrite Hty. apply mtype_of_MsgApp. }
      iDestruct (ents_ro with "Hents") as "#Hents"; first (rewrite Hty; w32_ne).
      iApply (dispatch_App with "Hinit Hphys Hghost Hents Hcap Hm' HΦ");
        [exact (A.wp_Step_MsgApp cfg r id s m ents)|done..|exact (Happ Hty)]. *)
      out_of_scope Hsm Hty. }
    destruct (decide (m.(raftpb.Message.Type') = MsgAppResp)) as [Hty|Hn_ar].
    { (* MsgAppResp: [dispatch_AppResp]. *)
      (* TO ENABLE: replace the next line by
      iDestruct ("Hmsg" $! mtype.AppResp with "[]") as "#Hm'".
      { iPureIntro. rewrite Hty. apply mtype_of_MsgAppResp. }
      iDestruct (ents_ro with "Hents") as "#Hents"; first (rewrite Hty; w32_ne).
      iApply (dispatch_AppResp with "Hinit Hphys Hghost Hents Hm' HΦ");
        [exact (AR.wp_Step_MsgAppResp cfg r id s m ents)|done..|exact (Happresp Hty)]. *)
      out_of_scope Hsm Hty. }
    destruct (decide (m.(raftpb.Message.Type') = MsgHeartbeat)) as [Hty|Hn_hb].
    { (* MsgHeartbeat: [dispatch_Heartbeat]. *)
      (* TO ENABLE: replace the next line by
      iDestruct ("Hmsg" $! mtype.Heartbeat with "[]") as "#Hm'".
      { iPureIntro. rewrite Hty. apply mtype_of_MsgHeartbeat. }
      iDestruct (ents_ro with "Hents") as "#Hents"; first (rewrite Hty; w32_ne).
      iApply (dispatch_Heartbeat with "Hinit Hphys Hghost Hents Hm' HΦ");
        [exact (HB.wp_Step_MsgHeartbeat cfg r id s m ents)|done..|exact (Hhb Hty)]. *)
      out_of_scope Hsm Hty. }
    destruct (decide (m.(raftpb.Message.Type') = MsgHeartbeatResp)) as [Hty|Hn_hr].
    { (* MsgHeartbeatResp: [dispatch_HeartbeatResp]; the [Context] is empty. *)
      (* TO ENABLE: replace the next line by
      iDestruct ("Hmsg" $! mtype.HeartbeatResp with "[]") as "#Hm'".
      { iPureIntro. rewrite Hty. apply mtype_of_MsgHeartbeatResp. }
      iDestruct (ents_ro with "Hents") as "#Hents"; first (rewrite Hty; w32_ne).
      iDestruct "Hctx" as (ctx) "(#Hctxp & _ & %Hctx0)".
      rewrite (Hctx0 Hty).
      iApply (dispatch_HeartbeatResp with "Hinit Hphys Hghost Hents Hctxp Hm' HΦ");
        [exact (HR.wp_Step_MsgHeartbeatResp cfg r id s m ents)|done..|exact (Hhbresp Hty)]. *)
      out_of_scope Hsm Hty. }
    destruct (decide (m.(raftpb.Message.Type') = MsgBeat)) as [Hty|Hn_beat].
    { (* MsgBeat: [dispatch_Beat]. *)
      (* TO ENABLE: replace the next line by
      iApply (dispatch_Beat with "Hinit Hphys Hghost HΦ");
        [exact (B.wp_Step_MsgBeat cfg r id s m)|done..|exact (Hbeat Hty)]. *)
      out_of_scope Hsm Hty. }
    destruct (decide (m.(raftpb.Message.Type') = MsgProp)) as [Hty|Hn_prop].
    { (* MsgProp: forward, append or drop ([proof_raft__Step_MsgProp.v]).
         The node's own [lead_ok] is what the follower's forwarding needs. *)
      destruct (Hprop Hty) as [Hterm Hfrom].
      destruct (Hpents Hty) as (Hne & Hnorm & Hlen).
      iDestruct (own_raft_ghost_lead_ok with "Hghost") as %Hlok.
      iDestruct ("Hmsg" $! mtype.Propose with "[]") as "#Hm'".
      { iPureIntro. rewrite Hty. apply mtype_of_MsgProp. }
      iDestruct (ents_own with "Hents") as "Hents"; first exact Hty.
      wp_apply (M.wp_Step_MsgProp cfg r id s m ents Hty Hterm Hfrom Hne Hnorm Hlen Hlok Hin Hwf
                 with "[$Hinit $Hphys $Hents $Hcap]").
      iIntros (err s') "(Hphys & %Hwf' & %Hst & Herr)".
      destruct Hst as (recv & Hrecv & Hstep).
      iApply (finish_branch with "Hm' Hghost Hphys [Herr] HΦ"); [done..|].
      iDestruct "Herr" as "[%Herr|#Hd]"; [iLeft; by iPureIntro|iRight; by iFrame "#"]. }
    (* none of the nine *)
    exfalso. cbv [step_msg step_msg_types step_msg_all] in Hsm.
    repeat (apply elem_of_cons in Hsm as [Hsm|Hsm]; [congruence|]).
    by apply elem_of_nil in Hsm.
  Qed.

End StepProof.

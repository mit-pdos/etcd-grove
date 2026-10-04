Require Export New.proof.go_etcd_io.raft.election_proof.postulates_stepLeader.

Module StepLeaderProof (P : STEPLEADER_POSTULATES) : STEPLEADER.
Import P.

Section helpers.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : raft.Assumptions}.
Collection W := sem + package_sem.
Set Default Proof Using "W".

Context (cfg : gset w64).

(** One peer's [Progress], borrowed out of a struct whose [Progress] values
    are [pvs] and given back at new values, keeping the state of the shape
    [s <| prvals := _ |>] (so that a run of writes does not pile up record
    updates). *)
Lemma own_raft_phys_pr_at r id s pvs to pr p :
  own_raft_phys cfg r id (s <| nstate.prvals := pvs |>) -∗
  ⌜ s.(nstate.progress) !! to = Some pr ⌝ -∗
  ⌜ pvs !! to = Some p ⌝ -∗
  own_Progress pr p ∗
  (∀ p', own_Progress pr p' -∗
     own_raft_phys cfg r id (s <| nstate.prvals := <[to := p']> pvs |>)).
Proof.
  iIntros "Hphys %Hlk %Hv".
  iDestruct (own_raft_phys_pr_upd with "Hphys [//] [//]") as "[Hp Hback]".
  iFrame "Hp". iIntros (p') "Hp".
  iDestruct ("Hback" with "Hp") as "Hphys".
  iApply (own_raft_phys_eq with "Hphys"). reflexivity.
Qed.

Lemma own_raft_phys_ins_id r id s pvs k a :
  pvs !! k = Some a →
  own_raft_phys cfg r id (s <| nstate.prvals := <[k := a]> pvs |>) -∗
  own_raft_phys cfg r id (s <| nstate.prvals := pvs |>).
Proof. iIntros (Hk) "H". iApply (own_raft_phys_eq with "H"). rewrite insert_id //. Qed.

Lemma own_raft_phys_prvals_self r id s :
  own_raft_phys cfg r id s -∗ own_raft_phys cfg r id (s <| nstate.prvals := s.(nstate.prvals) |>).
Proof. iIntros "H". iApply (own_raft_phys_eq with "H"). by destruct s. Qed.

Lemma send_msgs_nil_prvals s pvs :
  send_msgs s [] <| nstate.prvals := pvs |> = s <| nstate.prvals := pvs |>.
Proof. rewrite /send_msgs app_nil_r. by destruct s. Qed.

Lemma send_msgs_app2 s ms1 ms2 pvs pvs' :
  send_msgs (send_msgs s ms1 <| nstate.prvals := pvs |>) ms2 <| nstate.prvals := pvs' |> =
  send_msgs s (ms1 ++ ms2) <| nstate.prvals := pvs' |>.
Proof. rewrite /send_msgs /= app_assoc //. Qed.

(** The commit index set to what it already is. *)
Lemma commit_same s ms pvs pvs' :
  send_msgs (s <| nstate.prvals := pvs' |>) ms <| nstate.prvals := pvs |> =
  send_msgs (s <| nstate.logst := s.(nstate.logst) <| logstate.committed :=
                                    s.(nstate.logst).(logstate.committed) |> |>) ms
    <| nstate.prvals := pvs |>.
Proof. by destruct s as [?????????[]??]. Qed.

Lemma commit_same_nil s pvs :
  s <| nstate.prvals := pvs |> =
  send_msgs (s <| nstate.logst := s.(nstate.logst) <| logstate.committed :=
                                    s.(nstate.logst).(logstate.committed) |> |>) []
    <| nstate.prvals := pvs |>.
Proof. rewrite /send_msgs app_nil_r. by destruct s as [?????????[]??]. Qed.

(** [Match] under the [Progress] methods [stepLeader] calls. *)
Lemma decr_to_match p a b :
  (progress_maybe_decr_to p a b).2.(progress.matched) = p.(progress.matched).
Proof. rewrite /progress_maybe_decr_to. repeat case_decide; done. Qed.

Lemma become_probe_match p :
  (progress_become_probe p).(progress.matched) = p.(progress.matched).
Proof. done. Qed.

Lemma maybe_update_match p n :
  (progress_maybe_update p n).(progress.matched) =
  if decide (uint.Z p.(progress.matched) < uint.Z n) then n
  else p.(progress.matched).
Proof. rewrite /progress_maybe_update. case_bool_decide; case_decide; done. Qed.

(** The type switches: rewrite the message type to its literal and let
    [wp_auto] decide the comparisons. *)
Local Ltac first_switch_skip Hty lit :=
  rewrite Hty /lit; rewrite bool_decide_eq_false_2; [|w32_ne]; wp_auto.

(** ** [MsgVoteResp], [MsgApp], [MsgHeartbeat], [MsgPreVoteResp]: both
    switches fall through, whether or not the sender has a [Progress] *)
Lemma wp_stepLeader_noop r id s (m : raftpb.Message.t) :
  m.(raftpb.Message.Type') = MsgVoteResp ∨ m.(raftpb.Message.Type') = MsgApp ∨
  m.(raftpb.Message.Type') = MsgHeartbeat ∨ m.(raftpb.Message.Type') = MsgPreVoteResp →
  {{{ is_pkg_init raft ∗ own_raft_phys cfg r id s }}}
    @! raft.stepLeader #r #m
  {{{ (err : error.t) (s' : nstate.t), RET #err;
      own_raft_phys cfg r id s' ∗ ⌜ err = interface.nil ⌝ ∗
      ⌜ leader_nonprop_result cfg id s m s' ⌝ }}}.
Proof.
  intros Hty.
  wp_start as "Hphys".
  wp_auto.
  assert (m.(raftpb.Message.Type') = W32 6 ∨ m.(raftpb.Message.Type') = W32 3 ∨
          m.(raftpb.Message.Type') = W32 8 ∨ m.(raftpb.Message.Type') = W32 18) as Hl
    by exact Hty.
  destruct Hl as [Hl|[Hl|[Hl|Hl]]]; rewrite Hl;
    (rewrite bool_decide_eq_false_2; [|w32_ne]); wp_auto.
  all: iDestruct (own_raft_phys_tracker_same with "Hphys") as (tv) "(Htrkf & Htrk & Hback)".
  all: iDestruct (own_tracker_progress_map with "Htrk") as "(#Hprs & _ & Htrk)".
  all: wp_auto.
  all: iDestruct ("Hback" with "Htrkf Htrk") as "Hphys".
  all: wp_apply (wp_map_lookup1 with "Hprs") as "_".
  all: case_bool_decide as Hnil.
  all: wp_auto.
  all: try (wp_apply (wp_raft_load_id with "Hphys") as "Hphys"; wp_raft_log).
  all: try (rewrite Hl; (rewrite bool_decide_eq_false_2; [|w32_ne]); wp_auto).
  all: iApply ("HΦ" $! interface.nil s); iFrame "Hphys".
  all: iPureIntro; split; [done|]; left; split; [exact Hty|done].
Qed.

(** ** [MsgBeat]: [bcastHeartbeat], return *)
Lemma wp_stepLeader_beat r id s (m : raftpb.Message.t) :
  m.(raftpb.Message.Type') = MsgBeat →
  s.(nstate.role) = prole.Leader →
  {{{ is_pkg_init raft ∗ own_raft_phys cfg r id s }}}
    @! raft.stepLeader #r #m
  {{{ (err : error.t) (s' : nstate.t), RET #err;
      own_raft_phys cfg r id s' ∗ ⌜ err = interface.nil ⌝ ∗
      ⌜ leader_nonprop_result cfg id s m s' ⌝ }}}.
Proof.
  intros Hty Hlead.
  wp_start as "Hphys".
  wp_auto.
  rewrite Hty /MsgBeat bool_decide_eq_true_2 //.
  wp_auto.
  wp_apply (wp_raft__bcastHeartbeat _ _ _ _ Hlead with "[$Hphys]")
    as "%ms %pvs (Hphys & %Hms & %Hmm)".
  iApply ("HΦ" $! interface.nil). iFrame "Hphys".
  iPureIntro. split; [done|]. right; left. split; [done|].
  eexists _, _. split_and!; [reflexivity|done|done].
Qed.

(** The two ends of [MsgHeartbeatResp]'s [sendAppend] test. *)
Local Ltac hb_send :=
  wp_apply (wp_raft__sendAppend _ _ _ _ _ ltac:(eassumption) ltac:(eassumption)
              with "[$Hphys]") as "%ms %pvs (Hphys & %Hms & %Hmm)";
  iSplitR; [done|]; iExists _, _; iFrame "m r";
  iSplitL "Hphys"; [iApply (own_raft_phys_eq with "Hphys"); reflexivity|];
  iPureIntro; split; [eapply repl_sends_prvals; eassumption|];
  etrans; [eassumption|]; simpl; eassumption.
Local Ltac hb_skip :=
  iSplitR; [done|]; iExists [], _; iFrame "m r";
  iSplitL "Hphys";
  [ iApply (own_raft_phys_eq with "Hphys"); by rewrite send_msgs_nil_prvals
  | iPureIntro; split; [by apply Forall_nil|eassumption] ].

(** ** [MsgHeartbeatResp] *)
Lemma wp_stepLeader_hbresp r id s (m : raftpb.Message.t) :
  m.(raftpb.Message.Type') = MsgHeartbeatResp →
  s.(nstate.role) = prole.Leader →
  m.(raftpb.Message.From') ≠ id →
  {{{ is_pkg_init raft ∗ own_raft_phys cfg r id s ∗
      m.(raftpb.Message.Context') ↦*□ ([] : list w8) }}}
    @! raft.stepLeader #r #m
  {{{ (err : error.t) (s' : nstate.t), RET #err;
      own_raft_phys cfg r id s' ∗ ⌜ err = interface.nil ⌝ ∗
      ⌜ leader_nonprop_result cfg id s m s' ⌝ }}}.
Proof.
  intros Hty Hlead Hself.
  wp_start as "[Hphys #Hctx]".
  wp_auto.
  first_switch_skip Hty MsgHeartbeatResp.
  iDestruct (own_raft_phys_tracker_same with "Hphys") as (tv) "(Htrkf & Htrk & Hback)".
  iDestruct (own_tracker_progress_map with "Htrk") as "(#Hprs & %Hdom & Htrk)".
  iDestruct (own_tracker_prvals_dom with "Htrk") as "[%Hpdom Htrk]".
  wp_auto.
  iDestruct ("Hback" with "Htrkf Htrk") as "Hphys".
  wp_apply (wp_map_lookup1 with "Hprs") as "_".
  case_bool_decide as Hnil.
  { (* no [Progress] for the sender *)
    wp_auto.
    (wp_apply (wp_raft_load_id with "Hphys") as "Hphys"; wp_raft_log).
    iApply ("HΦ" $! interface.nil s). iFrame "Hphys".
    iPureIntro. split; [done|]. right; right; left. split; [done|].
    exists [], s.(nstate.prvals). split_and!; [|by apply Forall_nil|done].
    rewrite /send_msgs app_nil_r. by destruct s. }
  destruct (s.(nstate.progress) !! m.(raftpb.Message.From')) as [pr|] eqn:Hlk;
    [|by exfalso].
  simpl in Hnil.
  assert (m.(raftpb.Message.From') ∈ cfg) as Hfcfg.
  { rewrite -Hdom elem_of_dom Hlk. by eexists. }
  assert (is_Some (s.(nstate.prvals) !! m.(raftpb.Message.From'))) as [p Hpvs].
  { apply elem_of_dom. rewrite Hpdom elem_of_dom Hlk. by eexists. }
  clear Hdom Hpdom.
  wp_auto.
  rewrite Hty /MsgHeartbeatResp.
  rewrite bool_decide_eq_false_2; last w32_ne.
  wp_auto.
  (* [pr.RecentActive = true; pr.MsgAppFlowPaused = false] *)
  iDestruct (own_raft_phys_prvals_self with "Hphys") as "Hphys".
  iDestruct (own_raft_phys_pr_at with "Hphys [//] [//]") as "[Hpa Hpback]".
  iNamed "Hpa".
  wp_auto.
  set (p1 := p <| progress.recent_active := true |> <| progress.paused := false |>).
  iDestruct ("Hpback" $! p1 with "[Hpv Hinfl]") as "Hphys".
  { iExists _. iFrame "Hpv Hinfl". iPureIntro.
    rewrite /p1. progress_abs_from Habs. }
  clear Habs.
  set (pvs1 := <[m.(raftpb.Message.From') := p1]> s.(nstate.prvals)).
  assert (Hpvs1 : pvs1 !! m.(raftpb.Message.From') = Some p1)
    by (rewrite /pvs1 lookup_insert_eq //).
  assert (Hmm1 : prvals_match pvs1 = prvals_match s.(nstate.prvals))
    by (apply (prvals_match_insert_same _ _ p); done).
  (* [if pr.Match < r.raftLog.lastIndex() || pr.State == StateProbe
       { r.sendAppend(m.From) }], joined *)
  wp_bind (if: _ then _ else _)%E.
  iApply (wp_wand _ _ _
            (λ v, ⌜ v = execute_val ⌝ ∗
              ∃ ms pvs,
                "Hphys" ∷ own_raft_phys cfg r id (send_msgs s ms <| nstate.prvals := pvs |>) ∗
                "%Hms" ∷ ⌜ repl_sends id s ms ⌝ ∗
                "%Hmm" ∷ ⌜ prvals_match pvs = prvals_match s.(nstate.prvals) ⌝ ∗
                "m" ∷ m_ptr ↦ m ∗ "r" ∷ r_ptr ↦ r)%I
            with "[Hphys m r pr]").
  { wp_apply (wp_raft_load_raftLog with "Hphys") as "Hphys".
    iDestruct (own_raft_phys_log_same with "Hphys") as "[Hlog Hlogback]".
    wp_apply (wp_raftLog__lastIndex with "[$Hlog]") as "%li [Hlog %Hli]".
    iDestruct ("Hlogback" with "Hlog") as "Hphys".
    wp_if_destruct.
    { hb_send. }
    iDestruct (own_raft_phys_pr with "Hphys [//] [//]") as "[Hpa Hpback]".
    iNamed "Hpa".
    wp_auto.
    iDestruct ("Hpback" with "[Hpv Hinfl]") as "Hphys".
    { iExists _. iFrame "∗%". }
    wp_if_destruct.
    { hb_send. }
    hb_skip. }
  iIntros (v) "[-> HR]". iNamed "HR".
  wp_auto.
  (* [if r.readOnly.option != ReadOnlySafe || len(m.Context) == 0 { return nil }] *)
  iDestruct (own_raft_phys_readOnly with "Hphys") as (ro rr Hpend) "(Hrof & Hro & Hback)".
  iDestruct (own_ReadOnly_option with "Hro") as (o) "[%Hsafe [Hopt Hroback]]".
  wp_auto.
  iDestruct ("Hroback" with "Hopt") as "Hro".
  iDestruct ("Hback" with "[//] Hrof Hro") as "Hphys".
  iDestruct (own_slice_len with "Hctx") as %[Hcl Hcl0].
  assert (Hcz : m.(raftpb.Message.Context').(slice.len) = W64 0) by (simpl in Hcl; word).
  iAssert (Φ #interface.nil) with "[HΦ Hphys]" as "HΦ".
  { iApply ("HΦ" $! interface.nil (send_msgs s ms <| nstate.prvals := pvs |>)).
    iFrame "Hphys". iPureIntro. split; [done|]. right; right; left. split; [done|].
    eexists _, _. split_and!; [reflexivity|done|done]. }
  destruct (decide (o = W64 0)) as [Ho|Ho].
  - rewrite bool_decide_eq_true_2 //. wp_auto.
    rewrite Hcz. wp_auto. done.
  - rewrite bool_decide_eq_false_2 //. wp_auto. done.
Qed.

(** [repl_sends] reads only the term and the log ([repl_ok_proper]). *)
Lemma repl_sends_eq id (s1 s2 : nstate.t) ms :
  s1.(nstate.term) = s2.(nstate.term) →
  s1.(nstate.logst) = s2.(nstate.logst) →
  repl_sends id s1 ms → repl_sends id s2 ms.
Proof.
  intros Ht Hl. rewrite /repl_sends. apply Forall_impl. intros m'.
  apply repl_ok_proper; rewrite /to_pstate /= ?Ht ?Hl //.
Qed.

(** ** [MsgAppResp] *)
Lemma wp_stepLeader_appresp r id s (m : raftpb.Message.t) :
  m.(raftpb.Message.Type') = MsgAppResp →
  s.(nstate.role) = prole.Leader →
  id ∈ cfg →
  m.(raftpb.Message.From') ≠ W64 0 →
  (m.(raftpb.Message.Reject') = true → m.(raftpb.Message.From') ≠ id) →
  {{{ is_pkg_init raft ∗ own_raft_phys cfg r id s }}}
    @! raft.stepLeader #r #m
  {{{ (err : error.t) (s' : nstate.t), RET #err;
      own_raft_phys cfg r id s' ∗ ⌜ err = interface.nil ⌝ ∗
      ⌜ leader_nonprop_result cfg id s m s' ⌝ }}}.
Proof.
  intros Hty Hlead Hid Hfrom0 Hself.
  wp_start as "Hphys".
  wp_auto.
  first_switch_skip Hty MsgAppResp.
  iDestruct (own_raft_phys_tracker_same with "Hphys") as (tv) "(Htrkf & Htrk & Hback)".
  iDestruct (own_tracker_progress_map with "Htrk") as "(#Hprs & %Hdom & Htrk)".
  iDestruct (own_tracker_prvals_dom with "Htrk") as "[%Hpdom Htrk]".
  wp_auto.
  iDestruct ("Hback" with "Htrkf Htrk") as "Hphys".
  wp_apply (wp_map_lookup1 with "Hprs") as "_".
  case_bool_decide as Hnil.
  { (* no [Progress] for the sender (a [Progress] pointer is never nil) *)
    iAssert (⌜ m.(raftpb.Message.From') ∉ dom s.(nstate.progress) ⌝ ∗
             own_raft_phys cfg r id s)%I with "[Hphys]" as "[%Hnd Hphys]".
    { destruct (s.(nstate.progress) !! m.(raftpb.Message.From')) as [pr|] eqn:Hlk;
        [|iFrame; iPureIntro; by apply not_elem_of_dom].
      simpl in Hnil. subst pr.
      assert (is_Some (s.(nstate.prvals) !! m.(raftpb.Message.From'))) as [p Hpvs].
      { apply elem_of_dom. rewrite Hpdom elem_of_dom Hlk. by eexists. }
      iDestruct (own_raft_phys_pr with "Hphys [//] [//]") as "[Hpa _]".
      iNamed "Hpa".
      iDestruct (typed_pointsto_not_null with "Hpv") as %Hnn. done. }
    wp_auto.
    (wp_apply (wp_raft_load_id with "Hphys") as "Hphys"; wp_raft_log).
    iApply ("HΦ" $! interface.nil s). iFrame "Hphys".
    iPureIntro. split; [done|]. right; right; right. split; [done|].
    left. done. }
  destruct (s.(nstate.progress) !! m.(raftpb.Message.From')) as [pr|] eqn:Hlk;
    [|by exfalso].
  simpl in Hnil.
  assert (m.(raftpb.Message.From') ∈ cfg) as Hfcfg.
  { rewrite -Hdom elem_of_dom Hlk. by eexists. }
  assert (m.(raftpb.Message.From') ∈ dom s.(nstate.progress)) as Hfdom.
  { rewrite elem_of_dom Hlk. by eexists. }
  assert (is_Some (s.(nstate.prvals) !! m.(raftpb.Message.From'))) as [p Hpvs].
  { apply elem_of_dom. rewrite Hpdom elem_of_dom Hlk. by eexists. }
  clear Hdom Hpdom.
  wp_auto.
  rewrite Hty /MsgAppResp.
  rewrite bool_decide_eq_true_2 //.
  wp_auto.
  (* [pr.RecentActive = true] *)
  iDestruct (own_raft_phys_prvals_self with "Hphys") as "Hphys".
  iDestruct (own_raft_phys_pr_at with "Hphys [//] [//]") as "[Hpa Hpback]".
  iNamed "Hpa".
  wp_auto.
  set (p1 := p <| progress.recent_active := true |>).
  iDestruct ("Hpback" $! p1 with "[Hpv Hinfl]") as "Hphys".
  { iExists _. iFrame "Hpv Hinfl". iPureIntro.
    rewrite /p1. progress_abs_from Habs. }
  clear Habs.
  set (pvs1 := <[m.(raftpb.Message.From') := p1]> s.(nstate.prvals)).
  assert (Hpvs1 : pvs1 !! m.(raftpb.Message.From') = Some p1)
    by (rewrite /pvs1 lookup_insert_eq //).
  assert (Hmm1 : prvals_match pvs1 = prvals_match s.(nstate.prvals))
    by (apply (prvals_match_insert_same _ _ p); done).
  clearbody pvs1.
  destruct (m.(raftpb.Message.Reject')) eqn:Hrej.
  { (* rejected *)
    specialize (Hself eq_refl).
    wp_auto.
    (wp_apply (wp_raft_load_id with "Hphys") as "Hphys"; wp_raft_log).
    (* [nextProbeIdx], from [findConflictByTerm] when [m.LogTerm > 0] *)
    wp_if_join (λ v, ⌜ v = execute_val ⌝ ∗ ∃ np : w64,
                  "nextProbeIdx" ∷ nextProbeIdx_ptr ↦ np ∗
                  "Hphys" ∷ own_raft_phys cfg r id (s <| nstate.prvals := pvs1 |>) ∗
                  "m" ∷ m_ptr ↦ m ∗ "r" ∷ r_ptr ↦ r)%I
      with "[nextProbeIdx Hphys m r]".
    { wp_apply (wp_raft_load_raftLog with "Hphys") as "Hphys".
      iDestruct (own_raft_phys_log_same with "Hphys") as "[Hlog Hlogback]".
      wp_apply (wp_raftLog__findConflictByTerm with "[$Hlog]") as "%i' %t' [Hlog _]".
      iDestruct ("Hlogback" with "Hlog") as "Hphys".
      iSplitR; first done. iExists _. iFrame. }
    { iSplitR; first done. iExists _. iFrame. }
    iIntros (v) "[-> HR]". iNamed "HR".
    wp_auto.
    (* [pr.MaybeDecrTo(m.Index, nextProbeIdx)] *)
    iDestruct (own_raft_phys_pr_at with "Hphys [//] [//]") as "[Hpa Hpback]".
    wp_apply (wp_Progress__MaybeDecrTo with "[$Hpa]") as "Hpa".
    set (p2 := (progress_maybe_decr_to p1 m.(raftpb.Message.Index') np).2).
    iDestruct ("Hpback" $! p2 with "Hpa") as "Hphys".
    set (pvs2 := <[m.(raftpb.Message.From') := p2]> pvs1).
    assert (Hpvs2 : pvs2 !! m.(raftpb.Message.From') = Some p2)
      by (rewrite /pvs2 lookup_insert_eq //).
    assert (Hmm2 : prvals_match pvs2 = prvals_match s.(nstate.prvals)).
    { rewrite -Hmm1. apply (prvals_match_insert_same _ _ p1); [done|].
      apply decr_to_match. }
    clearbody pvs2.
    destruct ((progress_maybe_decr_to p1 m.(raftpb.Message.Index') np).1) eqn:Hdec.
    2:{ (* nothing to resend *)
      wp_auto.
      iApply ("HΦ" $! interface.nil (s <| nstate.prvals := pvs2 |>)). iFrame "Hphys".
      iPureIntro. split; [done|]. right; right; right. split; [done|].
      right; left. split_and!; [done|done|].
      exists [], pvs2. split_and!; [by rewrite send_msgs_nil_prvals|by apply Forall_nil|done]. }
    wp_auto.
    (wp_apply (wp_raft_load_id with "Hphys") as "Hphys"; wp_raft_log).
    (* [if pr.State == StateReplicate { pr.BecomeProbe() }] *)
    iDestruct (own_raft_phys_pr_at with "Hphys [//] [//]") as "[Hpa Hpback]".
    iNamed "Hpa".
    pose proof Habs as Hst2. apply progress_abs_Some in Hst2 as (_ & Hst2 & _).
    wp_auto. rewrite Hst2.
    iAssert (own_Progress pr p2) with "[Hpv Hinfl]" as "Hpa".
    { iExists _. iFrame "∗%". }
    clear Habs.
    destruct (decide (p2.(progress.state) = prstate.Replicate)) as [Hrep|Hrep].
    - rewrite bool_decide_eq_true_2; last by rewrite Hrep. wp_auto.
      wp_apply (wp_Progress__BecomeProbe with "[$Hpa]") as "Hpa".
      iDestruct ("Hpback" with "Hpa") as "Hphys".
      wp_apply (wp_raft__sendAppend _ _ _ _ _ Hself Hfcfg with "[$Hphys]")
        as "%ms %pvs (Hphys & %Hms & %Hmm)".
      iApply ("HΦ" $! interface.nil). iFrame "Hphys".
      iPureIntro. split; [done|]. right; right; right. split; [done|].
      right; left. split_and!; [done|done|].
      exists ms, pvs. split_and!; [reflexivity| |].
      + eapply repl_sends_eq; [..|exact Hms]; done.
      + rewrite Hmm /= -Hmm2. apply (prvals_match_insert_same _ _ p2); [done|].
        apply become_probe_match.
    - rewrite bool_decide_eq_false_2; last exact (prstate_w64_ne _ prstate.Replicate Hrep).
      wp_auto.
      iDestruct ("Hpback" with "Hpa") as "Hphys".
      wp_apply (wp_raft__sendAppend _ _ _ _ _ Hself Hfcfg with "[$Hphys]")
        as "%ms %pvs (Hphys & %Hms & %Hmm)".
      iApply ("HΦ" $! interface.nil). iFrame "Hphys".
      iPureIntro. split; [done|]. right; right; right. split; [done|].
      right; left. split_and!; [done|done|].
      exists ms, pvs. split_and!; [reflexivity| |].
      + eapply repl_sends_eq; [..|exact Hms]; done.
      + rewrite Hmm /= -Hmm2. apply (prvals_match_insert_same _ _ p2); done. }
  (* accepted *)
  wp_auto.
  (* [pr.MaybeUpdate(m.Index) || (pr.Match == m.Index && pr.State == StateProbe)]:
     its value does not matter to the postcondition, only that [pr] is
     left at [MaybeUpdate]'s value *)
  iDestruct (own_raft_phys_pr_at with "Hphys [//] [//]") as "[Hpa Hpback]".
  set (p2 := progress_maybe_update p1 m.(raftpb.Message.Index')).
  wp_bind (If _ #true _)%E.
  iApply (wp_wand _ _ _ (λ v, ∃ c : bool, ⌜ v = #c ⌝ ∗ own_Progress pr p2 ∗
                           "m" ∷ m_ptr ↦ m ∗ "pr" ∷ pr_ptr ↦ default null (Some pr))%I
            with "[Hpa m pr]").
  { wp_apply (wp_Progress__MaybeUpdate with "[$Hpa]") as "Hpa".
    iNamed "Hpa".
    wp_if_destruct.
    - iExists true. iSplitR; [done|]. iFrame "m pr". iExists _. iFrame "∗%".
    - wp_if_destruct.
      + iExists _. iSplitR; [done|]. iFrame "m pr". iExists _. iFrame "∗%".
      + iExists false. iSplitR; [done|]. iFrame "m pr". iExists _. iFrame "∗%". }
  iIntros (v) "(%c & -> & Hpa & m & pr)".
  iDestruct ("Hpback" $! p2 with "Hpa") as "Hphys".
  set (x := p.(progress.matched)).
  set (Mx := if decide (uint.Z x < uint.Z m.(raftpb.Message.Index'))
             then m.(raftpb.Message.Index') else x).
  assert (Hx : prvals_match s.(nstate.prvals) !! m.(raftpb.Message.From') = Some x)
    by (rewrite /prvals_match lookup_fmap Hpvs //).
  set (pvs2 := <[m.(raftpb.Message.From') := p2]> pvs1).
  assert (Hpvs2 : pvs2 !! m.(raftpb.Message.From') = Some p2)
    by (rewrite /pvs2 lookup_insert_eq //).
  assert (Hmm2 : prvals_match pvs2 =
                 <[m.(raftpb.Message.From') := Mx]> (prvals_match s.(nstate.prvals))).
  { rewrite /pvs2 /prvals_match fmap_insert. rewrite -/(prvals_match pvs1) Hmm1 /=.
    rewrite /p2 maybe_update_match //. }
  clearbody pvs2.
  destruct c.
  2:{ (* nothing to do *)
    wp_auto.
    iApply ("HΦ" $! interface.nil (s <| nstate.prvals := pvs2 |>)). iFrame "Hphys".
    iPureIntro. split; [done|]. right; right; right. split; [done|].
    right; right. split_and!; [done|done|].
    exists x, pvs2, s.(nstate.logst).(logstate.committed), [].
    split_and!; [done|done|by left|by apply Forall_nil|].
    rewrite send_msgs_nil_prvals. by destruct s as [?????????[]??]. }
  wp_auto.
  (* the [switch] on [pr.State], joined: [Match] does not move *)
  wp_bind (if: _ then _ else _)%E.
  iApply (wp_wand _ _ _
    (λ v, ⌜ v = execute_val ⌝ ∗ ∃ p3,
       "Hphys" ∷ own_raft_phys cfg r id
                   (s <| nstate.prvals := <[m.(raftpb.Message.From') := p3]> pvs2 |>) ∗
       "%Hm3" ∷ ⌜ p3.(progress.matched) = p2.(progress.matched) ⌝ ∗
       "m" ∷ m_ptr ↦ m ∗ "r" ∷ r_ptr ↦ r ∗ "pr" ∷ pr_ptr ↦ default null (Some pr))%I
    with "[Hphys m r pr]").
  { iDestruct (own_raft_phys_pr_at with "Hphys [//] [//]") as "[Hpa Hpback]".
    iNamed "Hpa".
    pose proof Habs as Hsm. apply progress_abs_Some in Hsm as (_ & Hst & Hm & _).
    wp_auto. rewrite Hst.
    destruct (decide (p2.(progress.state) = prstate.Probe)) as [Hst0|Hst0].
    { (* [StateProbe]: [BecomeReplicate] *)
      rewrite (bool_decide_eq_true_2 (prstate_w64 p2.(progress.state) = W64 0));
        last by rewrite Hst0.
      rewrite (bool_decide_eq_true_2 (true = true)) //.
      wp_auto.
      iAssert (own_Progress pr p2) with "[Hpv Hinfl]" as "Hpa".
      { iExists _. iFrame "∗%". }
      wp_apply (wp_Progress__BecomeReplicate with "[$Hpa]") as "Hpa".
      iDestruct ("Hpback" with "Hpa") as "Hphys".
      iSplitR; [done|]. iExists _. iFrame "Hphys m r pr". done. }
    rewrite (bool_decide_eq_false_2 (prstate_w64 p2.(progress.state) = W64 0));
      last exact (prstate_w64_ne _ prstate.Probe Hst0).
    rewrite (bool_decide_eq_false_2 (true = false)) //.
    wp_auto.
    destruct (decide (p2.(progress.state) = prstate.Snapshot)) as [Hst2|Hst2].
    { (* [StateSnapshot]: [pr.Match + 1 >= r.raftLog.firstIndex()] *)
      rewrite ?Hst (bool_decide_eq_true_2 (prstate_w64 p2.(progress.state) = W64 2));
        last by rewrite Hst2.
      wp_auto. try rewrite Hm.
      iDestruct ("Hpback" $! p2 with "[Hpv Hinfl]") as "Hphys".
      { iExists _. iFrame "∗%". }
      clear Habs.
      iDestruct (own_raft_phys_ins_id with "Hphys") as "Hphys"; first done.
      wp_apply (wp_raft_load_raftLog with "Hphys") as "Hphys".
      iDestruct (own_raft_phys_log_same with "Hphys") as "[Hlog Hlogback]".
      wp_apply (wp_raftLog__firstIndex with "[$Hlog]") as "%fi [Hlog _]".
      iDestruct ("Hlogback" with "Hlog") as "Hphys".
      destruct (decide (uint.Z fi ≤ uint.Z (word.add p2.(progress.matched) (W64 1))))
        as [Hfi|Hfi].
      - (* back from needing a snapshot: [BecomeProbe], [BecomeReplicate] *)
        rewrite (bool_decide_eq_true_2 (uint.Z fi ≤ _)) //
                (bool_decide_eq_true_2 (true = true)) //.
        wp_auto.
        (wp_apply (wp_raft_load_id with "Hphys") as "Hphys"; wp_raft_log).
        iDestruct (own_raft_phys_pr_at with "Hphys [//] [//]") as "[Hpa Hpback]".
        wp_apply (wp_Progress__BecomeProbe with "[$Hpa]") as "Hpa".
        wp_apply (wp_Progress__BecomeReplicate with "[$Hpa]") as "Hpa".
        iDestruct ("Hpback" with "Hpa") as "Hphys".
        iSplitR; [done|]. iExists _. iFrame "Hphys m r pr".
        iPureIntro. reflexivity.
      - rewrite (bool_decide_eq_false_2 (uint.Z fi ≤ _)) //
                (bool_decide_eq_false_2 (true = false)) //.
        wp_auto.
        (* [pr.State == StateReplicate]: no, [StateSnapshot] *)
        iDestruct (own_raft_phys_pr_at with "Hphys [//] [//]") as "[Hpa Hpback]".
        clear Hst Hm. iNamed "Hpa".
        pose proof Habs as Hsm. apply progress_abs_Some in Hsm as (_ & Hst & _).
        wp_auto. rewrite Hst.
        rewrite (bool_decide_eq_false_2 (prstate_w64 p2.(progress.state) = W64 1));
          last exact (prstate_w64_ne p2.(progress.state) prstate.Replicate ltac:(by rewrite Hst2)).
        rewrite (bool_decide_eq_false_2 (true = false)) //.
        wp_auto.
        iDestruct ("Hpback" $! p2 with "[Hpv Hinfl]") as "Hphys".
        { iExists _. iFrame "∗%". }
        iSplitR; [done|]. iExists p2. iFrame "Hphys m r pr". done. }
    rewrite ?Hst (bool_decide_eq_false_2 (prstate_w64 p2.(progress.state) = W64 2));
      last exact (prstate_w64_ne _ prstate.Snapshot Hst2).
    wp_auto.
    destruct (decide (p2.(progress.state) = prstate.Replicate)) as [Hst1|Hst1].
    - (* [StateReplicate]: [pr.Inflights.FreeLE(m.Index)] *)
      rewrite ?Hst (bool_decide_eq_true_2 (prstate_w64 p2.(progress.state) = W64 1));
        last by rewrite Hst1.
      rewrite (bool_decide_eq_true_2 (true = true)) //.
      wp_auto.
      wp_apply (wp_Inflights__FreeLE with "[$Hinfl]") as "%i' [Hinfl _]".
      iDestruct ("Hpback" $! (p2 <| progress.infl := i' |>) with "[Hpv Hinfl]") as "Hphys".
      { iExists _. iFrame "Hpv Hinfl". iPureIntro.
        assert (Hst1' : prstate_w64 p2.(progress.state) = prstate_w64 prstate.Replicate)
          by (rewrite Hst1; done).
        progress_abs_from Habs. all: exact Hst1'. }
      iSplitR; [done|]. iExists _. iFrame "Hphys m r pr". done.
    - (* no fourth state *)
      exfalso. destruct (p2.(progress.state)); congruence. }
  iIntros (v) "[-> HJ]". iNamed "HJ".
  set (pvs3 := <[m.(raftpb.Message.From') := p3]> pvs2).
  assert (Hpvs3 : pvs3 !! m.(raftpb.Message.From') = Some p3)
    by (rewrite /pvs3 lookup_insert_eq //).
  assert (Hmm3 : prvals_match pvs3 = prvals_match pvs2)
    by (apply (prvals_match_insert_same _ _ p2); done).
  clearbody pvs3.
  wp_auto.
  (* [if r.maybeCommit() { release...; r.bcastAppend() } else if r.id != m.From &&
       pr.CanBumpCommit(r.raftLog.committed) { r.sendAppend(m.From) }], joined *)
  wp_bind (if: _ then _ else _)%E.
  iApply (wp_wand _ _ _
    (λ v, ⌜ v = execute_val ⌝ ∗ ∃ (c : w64) ms pvs4,
       "Hphys" ∷ own_raft_phys cfg r id
                   (send_msgs (s <| nstate.logst :=
                                 s.(nstate.logst) <| logstate.committed := c |> |>) ms
                      <| nstate.prvals := pvs4 |>) ∗
       "%Hc" ∷ ⌜ c = s.(nstate.logst).(logstate.committed) ∨
                 commit_ok cfg (to_pstate (s <| nstate.prvals := pvs3 |>)) c ⌝ ∗
       "%Hms" ∷ ⌜ repl_sends id (s <| nstate.logst :=
                                    s.(nstate.logst) <| logstate.committed := c |> |>) ms ⌝ ∗
       "%Hmm4" ∷ ⌜ prvals_match pvs4 = prvals_match pvs3 ⌝ ∗
       "m" ∷ m_ptr ↦ m ∗ "r" ∷ r_ptr ↦ r ∗ "pr" ∷ pr_ptr ↦ default null (Some pr))%I
    with "[Hphys m r pr]").
  { wp_apply (wp_raft__maybeCommit with "[$Hphys]"); [exact Hlead|exact Hid|].
    iIntros (b N) "[Hphys %HN]".
    destruct b.
    - (* committed: [releasePendingReadIndexMessages] is a no-op, then
         [bcastAppend] *)
      wp_auto.
      wp_apply (wp_releasePendingReadIndexMessages with "[$Hphys]") as "Hphys".
      wp_apply (wp_raft__bcastAppend with "[$Hphys]") as "%ms %pvs4 (Hphys & %Hms & %Hmm4)".
      iSplitR; [done|]. iExists N, ms, pvs4. iFrame "m r pr".
      iSplitL "Hphys".
      { iApply (own_raft_phys_eq with "Hphys"). reflexivity. }
      iPureIntro. split_and!.
      + right. by apply HN.
      + eapply repl_sends_eq; [..|exact Hms]; done.
      + rewrite Hmm4 //.
    - (* not committed: [r.id != m.From && pr.CanBumpCommit(r.raftLog.committed)] *)
      wp_auto.
      wp_apply (wp_raft_load_id with "Hphys") as "Hphys".
      destruct (decide (id = m.(raftpb.Message.From'))) as [Hsame|Hdiff].
      + (* the leader's own acknowledgement *)
        rewrite bool_decide_eq_true_2 //. wp_auto.
        iSplitR; [done|]. iExists s.(nstate.logst).(logstate.committed), [], pvs3.
        iFrame "m r pr".
        iSplitL "Hphys".
        { iApply (own_raft_phys_eq with "Hphys"). apply commit_same_nil. }
        iPureIntro. split_and!; [by left|by apply Forall_nil|done].
      + rewrite bool_decide_eq_false_2 //. wp_auto.
        wp_apply (wp_raft_load_raftLog with "Hphys") as "Hphys".
        iDestruct (own_raft_phys_log_same with "Hphys") as "[Hlog Hlogback]".
        iDestruct (own_raftLog_struct with "Hlog") as (lv) "(Hl & _ & Hlb)".
        wp_auto.
        iDestruct ("Hlb" with "Hl") as "Hlog".
        iDestruct ("Hlogback" with "Hlog") as "Hphys".
        iDestruct (own_raft_phys_pr_at with "Hphys [//] [//]") as "[Hpa Hpback]".
        wp_apply (wp_Progress__CanBumpCommit with "[$Hpa]") as "Hpa".
        iDestruct ("Hpback" $! p3 with "Hpa") as "Hphys".
        iDestruct (own_raft_phys_ins_id with "Hphys") as "Hphys"; first done.
        rewrite /progress_can_bump_commit. wp_if_destruct.
        * wp_apply (wp_raft__sendAppend _ _ _ _ _ (not_eq_sym Hdiff) Hfcfg with "[$Hphys]")
            as "%ms %pvs4 (Hphys & %Hms & %Hmm4)".
          iSplitR; [done|]. iExists s.(nstate.logst).(logstate.committed), ms, pvs4.
          iFrame "m r pr".
          iSplitL "Hphys".
          { iApply (own_raft_phys_eq with "Hphys"). apply commit_same. }
          iPureIntro. split_and!; [by left| |done].
          eapply repl_sends_eq; [..|exact Hms]; [done|]. simpl.
          by destruct (s.(nstate.logst)).
        * iSplitR; [done|]. iExists s.(nstate.logst).(logstate.committed), [], pvs3.
          iFrame "m r pr".
          iSplitL "Hphys".
          { iApply (own_raft_phys_eq with "Hphys"). apply commit_same_nil. }
          iPureIntro. split_and!; [by left|by apply Forall_nil|done]. }
  iIntros (v) "[-> HJ]". iNamed "HJ".
  wp_auto.
  set (sc := s <| nstate.logst := s.(nstate.logst) <| logstate.committed := c |> |>).
  (* [if r.id != m.From { for r.maybeSendAppend(m.From, false) {} }], joined *)
  wp_apply (wp_raft_load_id with "Hphys") as "Hphys".
  wp_bind (if: _ then _ else _)%E.
  iApply (wp_wand _ _ _
    (λ v, ⌜ v = execute_val ⌝ ∗ ∃ ms' pvs5,
       "Hphys" ∷ own_raft_phys cfg r id (send_msgs sc (ms ++ ms') <| nstate.prvals := pvs5 |>) ∗
       "%Hms'" ∷ ⌜ repl_sends id sc ms' ⌝ ∗
       "%Hmm5" ∷ ⌜ prvals_match pvs5 = prvals_match pvs4 ⌝ ∗
       "m" ∷ m_ptr ↦ m ∗ "r" ∷ r_ptr ↦ r)%I
    with "[Hphys m r]").
  { destruct (decide (id = m.(raftpb.Message.From'))) as [Hsame|Hdiff].
    { rewrite bool_decide_eq_true_2 //. wp_auto.
      iSplitR; [done|]. iExists [], pvs4. iFrame "m r".
      iSplitL "Hphys".
      { iApply (own_raft_phys_eq with "Hphys"). rewrite app_nil_r //. }
      iPureIntro. split; [by apply Forall_nil|done]. }
    rewrite bool_decide_eq_false_2 //. wp_auto.
    iAssert (∃ ms' pvs5,
       "Hphys" ∷ own_raft_phys cfg r id (send_msgs sc (ms ++ ms') <| nstate.prvals := pvs5 |>) ∗
       "%Hms'" ∷ ⌜ repl_sends id sc ms' ⌝ ∗
       "%Hmm5" ∷ ⌜ prvals_match pvs5 = prvals_match pvs4 ⌝ ∗
       "%Hne" ∷ ⌜ m.(raftpb.Message.From') ≠ id ⌝ ∗
       "%Hin" ∷ ⌜ m.(raftpb.Message.From') ∈ cfg ⌝ ∗
       "m" ∷ m_ptr ↦ m ∗ "r" ∷ r_ptr ↦ r)%I
      with "[Hphys m r]" as "IH".
    { iExists [], pvs4. iFrame "m r".
      iSplitL "Hphys".
      { iApply (own_raft_phys_eq with "Hphys"). rewrite app_nil_r //. }
      iPureIntro. split_and!; [by apply Forall_nil|done|done|done]. }
    wp_for "IH".
    wp_apply (wp_raft__maybeSendAppend _ _ _ _ _ false Hne Hin with "[$Hphys]")
      as "%b %ms'' %pvs'' (Hphys & %Hms'' & %Hmm'')".
    destruct b.
    - rewrite decide_True //. wp_auto. wp_for_post.
      iFrame "m r". iExists (ms' ++ ms''), pvs''.
      iSplitL "Hphys".
      { iApply (own_raft_phys_eq with "Hphys"). rewrite send_msgs_app2 app_assoc //. }
      iPureIntro. split_and!; [|by rewrite Hmm''|done|done].
      apply repl_sends_app; [done|]. eapply repl_sends_eq; [..|exact Hms'']; done.
    - rewrite decide_False // decide_True //.
      iSplitR; [done|]. iExists (ms' ++ ms''), pvs''. iFrame "m r".
      iSplitL "Hphys".
      { iApply (own_raft_phys_eq with "Hphys"). rewrite send_msgs_app2 app_assoc //. }
      iPureIntro. split; [|by rewrite Hmm''].
      apply repl_sends_app; [done|]. eapply repl_sends_eq; [..|exact Hms'']; done. }
  iIntros (v) "[-> HJ]". iNamed "HJ".
  wp_auto.
  (* [m.From == r.leadTransferee && ...]: [leadTransferee = 0 ≠ m.From], so
     [sendTimeoutNow] is not reached *)
  wp_apply (wp_raft_load_leadTransferee with "Hphys") as "Hphys".
  rewrite bool_decide_eq_false_2 //.
  wp_auto.
  iApply ("HΦ" $! interface.nil (send_msgs sc (ms ++ ms') <| nstate.prvals := pvs5 |>)).
  iFrame "Hphys". iPureIntro. split; [done|].
  right; right; right. split; [done|]. right; right. split_and!; [done|done|].
  assert (Hts : to_pstate (s <| nstate.prvals := pvs5 |>) =
                to_pstate (s <| nstate.prvals := pvs3 |>))
    by (rewrite /to_pstate /= Hmm5 Hmm4 //).
  exists x, pvs5, c, (ms ++ ms'). split_and!.
  - exact Hx.
  - rewrite Hmm5 Hmm4 Hmm3 Hmm2 //.
  - rewrite Hts //.
  - by apply repl_sends_app.
  - reflexivity.
Qed.


(** ** [MsgProp]

    [len(m.Entries) == 0] is false ([ents ≠ []]); [r.trk.Progress[r.id]]
    is a hit ([id ∈ cfg], and a [Progress] pointer is never nil);
    [r.leadTransferee] is [0]; the conf-change loop reads each entry's
    [Type] -- [EntryNormal], so neither [Unmarshal] arm runs and [cc] stays
    nil -- and writes nothing.  Then [appendEntry] stamps the batch and,
    if it accepts it, [bcastAppend]. *)
Lemma wp_stepLeader_prop r id s (m : raftpb.Message.t) ents :
  m.(raftpb.Message.Type') = MsgProp →
  id ∈ cfg →
  ents ≠ [] →
  Forall (λ e, e.(raftpb.Entry.Type') = EntryNormal) ents →
  (Z.of_nat (length ents) < 2^61)%Z →
  {{{ is_pkg_init raft ∗ own_raft_phys cfg r id s ∗
      m.(raftpb.Message.Entries') ↦* ents }}}
    @! raft.stepLeader #r #m
  {{{ (err : error.t) (s' : nstate.t) (dropped : bool), RET #err;
      own_raft_phys cfg r id s' ∗
      ⌜ leader_propose_result id s ents dropped s' ⌝ ∗
      (if dropped then (global_addr raft.ErrProposalDropped) ↦□ err
       else ⌜ err = interface.nil ⌝) ∗
      m.(raftpb.Message.Entries') ↦*
        imap (stamp s.(nstate.term) (log_last s.(nstate.logst))) ents }}}.
Proof.
  intros Hty Hid Hne Hnorm Hsmall.
  wp_start as "[Hphys Hes]".
  iDestruct (is_pkg_init_access with "[$]") as "@".
  wp_auto.
  rewrite Hty /MsgProp. rewrite bool_decide_eq_false_2; [|w32_ne]. wp_auto.
  iDestruct (own_slice_len with "Hes") as %[Hl1 Hl2].
  rewrite bool_decide_eq_false_2; last first.
  { intros Heq. apply Hne, length_zero_iff_nil. rewrite Hl1 Heq //. }
  wp_auto.
  wp_apply (wp_raft_load_id with "Hphys") as "Hphys".
  iDestruct (own_raft_phys_tracker_same with "Hphys") as (tv) "(Htrkf & Htrk & Hback)".
  iDestruct (own_tracker_progress_map with "Htrk") as "(#Hprs & %Hdom & Htrk)".
  iDestruct (own_tracker_prvals_dom with "Htrk") as "[%Hpdom Htrk]".
  cbn [trk.prs trk.peers] in Hdom, Hpdom.
  wp_auto.
  iDestruct ("Hback" with "Htrkf Htrk") as "Hphys".
  wp_apply (wp_map_lookup1 with "Hprs") as "_".
  destruct (s.(nstate.progress) !! id) as [pr|] eqn:Hlk; last first.
  { exfalso. apply not_elem_of_dom in Hlk. apply Hlk. by rewrite Hdom. }
  assert (is_Some (s.(nstate.prvals) !! id)) as [p Hpvs].
  { apply elem_of_dom. rewrite Hpdom elem_of_dom Hlk. by eexists. }
  iAssert (⌜ pr ≠ null ⌝ ∗ own_raft_phys cfg r id s)%I with "[Hphys]" as "[%Hnn Hphys]".
  { iDestruct (own_raft_phys_pr_upd with "Hphys [//] [//]") as "[Hpa Hpback]".
    iNamed "Hpa".
    iDestruct (typed_pointsto_not_null with "Hpv") as %Hnn.
    iSplitR; first done.
    iDestruct ("Hpback" with "[Hpv Hinfl]") as "Hphys".
    { iExists _. iFrame "∗%". }
    iApply (own_raft_phys_eq with "Hphys"). rewrite insert_id //. by destruct s. }
  clear Hdom Hpdom.
  simpl. rewrite bool_decide_eq_false_2 //.
  wp_auto.
  wp_apply (wp_raft_load_leadTransferee with "Hphys") as "Hphys".
  wp_alloc j as "Hj".
  iAssert (∃ (n k : w64),
    "Hj" ∷ j ↦ n ∗
    "i" ∷ i_ptr ↦ k ∗
    "Hes" ∷ m.(raftpb.Message.Entries') ↦* ents ∗
    "%Hnorm" ∷ ⌜ Forall (λ e, e.(raftpb.Entry.Type') = EntryNormal) ents ⌝ ∗
    "%Hsmall" ∷ ⌜ (Z.of_nat (length ents) < 2^61)%Z ⌝ ∗
    "%Hn" ∷ ⌜ (0 ≤ sint.Z n ≤ Z.of_nat (length ents))%Z ⌝)%I
    with "[Hj i Hes]" as "IH".
  { iExists (W64 0), _. iFrame. iPureIntro. split; [done|word]. }
  wp_auto.
  wp_for "IH".
  wp_if_destruct.
  - assert (∃ e, ents !! sint.nat n = Some e) as [e He].
    { apply lookup_lt_is_Some_2. word. }
    rewrite decide_True; last word.
    wp_apply (wp_load_slice_index (V:=raftpb.Entry.t) (t:=raftpb.Entry)
                _ (sint.Z n) _ (DfracOwn 1) e with "[$Hes]") as "Hes";
      try first [ word | iPureIntro; exact He | tc_solve | done ].
    try wp_auto.
    rewrite decide_True; last word.
    iDestruct (own_slice_elem_acc (sint.Z n) e _ (DfracOwn 1) _
                 with "Hes") as "[He Hesback]";
      [ word | rewrite -He; f_equal; word | ].
    wp_auto.
    assert (e.(raftpb.Entry.Type') = EntryNormal) as Hety.
    { rewrite List.Forall_forall in Hnorm. apply Hnorm, list_elem_of_In.
      by eapply list_elem_of_lookup_2. }
    rewrite Hety.
    wp_auto.
    rewrite Hety.
    wp_auto.
    iDestruct ("Hesback" with "He") as "Hes".
    rewrite list_insert_id; last (rewrite -He; f_equal; word).
    wp_for_post.
    iFrame. iPureIntro. split_and!; [done|done|word|word].
  - wp_apply (wp_raft__appendEntry _ _ _ _ _ _ Hnorm Hsmall with "[$Hphys $Hes]")
      as "%acc (_ & Hes & Hphys)".
    destruct acc; wp_auto.
    + wp_apply (wp_raft__bcastAppend with "[$Hphys]") as "%ms %pvs (Hphys & %Hms & %Hmm)".
      try wp_auto.
      iApply ("HΦ" $! interface.nil _ false). iFrame "Hphys Hes".
      iPureIntro. split; [|done].
      rewrite /leader_propose_result. exists ms, pvs. split_and!; [reflexivity|exact Hms|].
      rewrite Hmm. done.
    + iApply ("HΦ" $! errPropDropped s true). iFrame "Hphys Hes ErrPropDropped".
      done.
Qed.

End helpers.

Set Default Proof Using "Type".

  (** By the message type, one lemma each.  The non-[MsgProp] lemmas are
      stated at [leader_nonprop_result] with [err = nil]; [HΦ'] turns
      that into the postcondition with [dropped = false]. *)
  Lemma wp_stepLeader : wp_stepLeader_body.
  Proof.
    intros_ambient.
    intros cfg r id s m ents Hty Hlead Hid Hfrom0 Hself Hprop.
    iIntros (Φ) "(#Hinit & Hphys & Hctx & Hents) HΦ".
    destruct (decide (m.(raftpb.Message.Type') = MsgProp)) as [Hp|Hnp].
    { destruct (Hprop Hp) as (Hne & Hnorm & Hsmall).
      iDestruct ("Hents" with "[//]") as "Hes".
      iApply (wp_stepLeader_prop cfg r id s m ents Hp Hid Hne Hnorm Hsmall
                with "[$Hinit $Hphys $Hes]").
      iIntros "!>" (err s' dropped) "(Hphys & %Hres & Herr & Hes)".
      iApply ("HΦ" $! err s' dropped). iFrame "Hphys Herr".
      iSplitR.
      { iPureIntro. rewrite /leader_step_result decide_True //. }
      iIntros "_". iExact "Hes". }
    iAssert (▷ ∀ (err : error.t) (s' : nstate.t),
               own_raft_phys cfg r id s' ∗ ⌜ err = interface.nil ⌝ ∗
               ⌜ leader_nonprop_result cfg id s m s' ⌝ -∗ Φ #err)%I
      with "[HΦ]" as "HΦ'".
    { iIntros "!>" (err s') "(Hphys & %Herr & %Hres)".
      iApply ("HΦ" $! err s' false). iFrame "Hphys".
      iSplitR.
      { iPureIntro. rewrite /leader_step_result decide_False //. }
      iSplitR; first done.
      iIntros "%Hc". by exfalso. }
    destruct Hty as [Hty|[Hty|[Hty|[Hty|[Hty|[Hty|[Hty|Hty]]]]]]].
    - iApply (wp_stepLeader_noop cfg r id s m (or_introl Hty)
                with "[$Hinit $Hphys] HΦ'").
    - iApply (wp_stepLeader_beat cfg r id s m Hty Hlead with "[$Hinit $Hphys] HΦ'").
    - iDestruct ("Hctx" with "[//]") as "#Hc".
      iApply (wp_stepLeader_hbresp cfg r id s m Hty Hlead (Hself (or_introl Hty))
                with "[$Hinit $Hphys $Hc] HΦ'").
    - iApply (wp_stepLeader_appresp cfg r id s m Hty Hlead Hid (Hfrom0 Hty)
                (λ Hr, Hself (or_intror (conj Hty Hr)))
                with "[$Hinit $Hphys] HΦ'").
    - by exfalso.
    - iApply (wp_stepLeader_noop cfg r id s m (or_intror (or_introl Hty))
                with "[$Hinit $Hphys] HΦ'").
    - iApply (wp_stepLeader_noop cfg r id s m (or_intror (or_intror (or_introl Hty)))
                with "[$Hinit $Hphys] HΦ'").
    - iApply (wp_stepLeader_noop cfg r id s m (or_intror (or_intror (or_intror Hty)))
                with "[$Hinit $Hphys] HΦ'").
  Qed.

End StepLeaderProof.

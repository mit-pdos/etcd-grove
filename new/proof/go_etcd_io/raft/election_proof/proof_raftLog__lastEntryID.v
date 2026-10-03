Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raftLog__lastEntryID.

(** Until 2026-09-23 this file proved an internal form at a fixed split and
    derived the interface form, on the existential [own_raftLog l], from it.
    With the log indexed by its state there is one form. *)
(** The last entry's id, read off [lastIndex] and [term(lastIndex)]. *)
Local Lemma plog_last_eq (b : raft.entryID.t) (es : list raftpb.Entry.t) (t li : w64) :
  plog_wf b es →
  uint.Z li = plog_last_index_Z b es →
  plog_term_at b es li = Some t →
  raft.entryID.mk t li = plog_last b es.
Proof.
  intros Hwf Hli Ht.
  pose proof (plog_last_index b es Hwf) as Hidx.
  pose proof (plog_term_at_last b es Hwf) as Hterm.
  assert (li = (plog_last b es).(raft.entryID.index')) as Heq.
  { apply word.unsigned_inj. lia. }
  rewrite -Heq Ht in Hterm. injection Hterm as ->.
  rewrite Heq. by destruct (plog_last b es).
Qed.

Module RaftLogLastEntryIDProof (P : RAFTLOG__LASTENTRYID_POSTULATES) : RAFTLOG__LASTENTRYID.
Import P.

  Lemma wp_raftLog__lastEntryID : wp_raftLog__lastEntryID_body.
  Proof.
    intros_ambient.
    intros l ls.
    destruct ls as [prev sents uents lcm lap snap]; logstate_simpl.
    wp_start as "Hlog". wp_auto.
    wp_apply (wp_raftLog__lastIndex _ (logstate.mk prev sents uents lcm lap snap) with "[$Hlog]") as "%li [Hlog %Hli]". logstate_simpl.
    assert (Hb : (uint.Z prev.(raft.entryID.index') ≤ uint.Z li ≤
                  uint.Z prev.(raft.entryID.index') + Z.of_nat (length sents)
                  + Z.of_nat (length uents))%Z) by lia.
    (* [raftLog.term]'s triple is total ([spec_raftLog__term.v]); here the
       index is [lastIndex], so the in-range clause of its postcondition
       applies and the error is [nil] -- which is what makes the [Panicf]
       on the next line unreachable. *)
    wp_apply (wp_raftLog__term _ (logstate.mk prev sents uents lcm lap snap) _ with "[$Hlog]") as "%t %err (Hlog & %Herr & %Ht & _)". logstate_simpl.
    apply (proj2 Herr) in Hb. subst err. specialize (Ht eq_refl). wp_auto.
    iDestruct (own_raftLog_wf with "Hlog") as "[%Hwf Hlog]". logstate_simpl.
    iApply ("HΦ" $! (raft.entryID.mk t li)). iFrame. iPureIntro.
    apply plog_last_eq; [done | rewrite /plog_last_index_Z length_app; lia | done].
  Qed.
End RaftLogLastEntryIDProof.

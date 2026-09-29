Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raftLog__lastEntryID.

(** Until 2026-09-23 this file proved an internal form at a fixed split and
    derived the interface form, on the existential [own_raftLog l], from it.
    With the log indexed by its state there is one form. *)
Module RaftLogLastEntryIDProof (P : RAFTLOG__LASTENTRYID_POSTULATES) : RAFTLOG__LASTENTRYID.
Import P.

  Lemma wp_raftLog__lastEntryID : wp_raftLog__lastEntryID_body.
  Proof.
    intros_ambient.
    intros l ls.
    destruct ls as [prev sents uents lcm lap]; logstate_simpl.
    wp_start as "Hlog". wp_auto.
    wp_apply (wp_raftLog__lastIndex _ (logstate.mk prev sents uents lcm lap) with "[$Hlog]") as "%li [Hlog %Hli]". logstate_simpl.
    assert (Hb : (uint.Z prev.(raft.entryID.index') ≤ uint.Z li ≤
                  uint.Z prev.(raft.entryID.index') + Z.of_nat (length sents)
                  + Z.of_nat (length uents))%Z) by lia.
    (* [raftLog.term]'s triple is total ([spec_raftLog__term.v]); here the
       index is [lastIndex], so the in-range clause of its postcondition
       applies and the error is [nil] -- which is what makes the [Panicf]
       on the next line unreachable. *)
    wp_apply (wp_raftLog__term _ (logstate.mk prev sents uents lcm lap) _ with "[$Hlog]") as "%t %err [Hlog %Herr]". logstate_simpl.
    apply (proj2 Herr) in Hb. subst err. wp_auto.
    iApply ("HΦ" $! (raft.entryID.mk t li)). iFrame.
  Qed.
End RaftLogLastEntryIDProof.

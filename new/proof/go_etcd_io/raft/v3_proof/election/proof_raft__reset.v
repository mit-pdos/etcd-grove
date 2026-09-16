Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_raft__reset.

Module ResetProof (P : RESET_POSTULATES) : RESET.

Section helper.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : raft.Assumptions}.

Local Lemma raft_split_trk (l : loc) (rv : raft.raft.t) :
  l ↦ rv -∗
  l.[raft.raft.t, "trk"] ↦ rv.(raft.raft.trk') ∗
  (∀ tv, l.[raft.raft.t, "trk"] ↦ tv -∗ l ↦ (rv <| raft.raft.trk' := tv |>)).
Proof.
  iIntros "Hr".
  iEval (rewrite typed_pointsto_unseal /typed_pointsto_wrap /=) in "Hr".
  iDestruct "Hr" as "[Hf %Hnn]". iNamed "Hf".
  iFrame "trk".
  iIntros (tv) "Htv".
  iEval (rewrite typed_pointsto_unseal /typed_pointsto_wrap /=).
  iFrame "∗%".
Qed.

End helper.

  Local Ltac reset_tail r_ptr r rvC :=
    wp_apply (wp_ProgressTracker__Visit _ _ _ _ _
                (r_ptr ↦ r ∗ r ↦ rvC ∗ own_raftLog rvC.(raft.raft.raftLog'))%I
                with "[$Htrk $Hr $r $Hlog]") as "[Htrk (r & Hr & Hlog)]".

  Lemma wp_raft__reset : wp_raft__reset_body.
  Proof.
    intros_ambient.
    intros cfg r id s term.
    wp_start as "Hphys". iNamed "Hphys". wp_auto.
    destruct (decide (term = s.(nstate.term))) as [Heq|Hne].
    - assert (bool_decide (rv.(raft.raft.Term') = term) = true) as Hb
        by (apply bool_decide_eq_true_2; congruence).
      rewrite Hb /=. wp_auto.
      wp_apply (wp_raft__resetRandomizedElectionTimeout with "[$Hr]") as "%n Hr".
      wp_apply (wp_raft__abortLeaderTransfer with "[$Hr]") as "Hr".
      iDestruct (raft_split_trk with "Hr") as "[Htrkf Hrback]".
      wp_apply (wp_ProgressTracker__ResetVotes with "[$Htrkf $Htrk]")
        as "%votesRef [Htrkf Htrk]".
      iDestruct ("Hrback" with "Htrkf") as "Hr".
      reset_tail r_ptr r
        (rv <| raft.raft.lead' := W64 0 |>
            <| raft.raft.electionElapsed' := W64 0 |>
            <| raft.raft.heartbeatElapsed' := W64 0 |>
            <| raft.raft.randomizedElectionTimeout' := n |>
            <| raft.raft.leadTransferee' := W64 0 |>
            <| raft.raft.trk' := rv.(raft.raft.trk')
                 <| tracker.ProgressTracker.Votes' := votesRef |> |>).
      Show 1.
      all: admit.
    - admit.
  Admitted.

End ResetProof.

Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_raft__reset.

Module ResetProof (P : RESET_POSTULATES) : RESET.

Section helper.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : raft.Assumptions}.

(** Split the [trk] field out of the whole-struct points-to, keeping a wand
    that accepts *any* new tracker value.  The generated [AccessStrict]
    instance is not enough here: its [A'] fixes the new value, and the value
    [trk.ResetVotes()] installs is only introduced by that call's
    postcondition -- after the evar for [A'] has been created, so it is out of
    the evar's scope ("iSpecialize: cannot instantiate").  Quantifying inside
    the wand avoids the evar entirely. *)
Local Lemma raft_split_trk (l : loc) (rv : raft.raft.t) :
  l ↦ rv -∗
  l.[raft.raft.t, "trk"] ↦ rv.(raft.raft.trk') ∗
  (∀ tv, l.[raft.raft.t, "trk"] ↦ tv -∗ l ↦ (rv <| raft.raft.trk' := tv |>)).
Proof.
  iIntros "Hr".
  iEval (rewrite typed_pointsto_unseal /typed_pointsto_wrap /=) in "Hr".
  Show.
Admitted.

End helper.

Set Default Proof Using "Type".

  Lemma wp_raft__reset : wp_raft__reset_body.
  Proof.
  Admitted.

End ResetProof.

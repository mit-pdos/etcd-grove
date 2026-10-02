Require Export New.proof.go_etcd_io.raft.election_proof.postulates_releasePendingReadIndexMessages.

Module ReleasePendingReadIndexMessagesProof
  (P : RELEASEPENDINGREADINDEXMESSAGES_POSTULATES)
  : RELEASEPENDINGREADINDEXMESSAGES.

Section helpers.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : raft.Assumptions}.
Collection W := sem + package_sem.
Set Default Proof Using "W".

Context (cfg : gset w64).

(** The load of [r.pendingReadIndexMessages], at a slice of length [0].

    **This belongs in the interface section of [inv_raft_phys.v]**, beside
    the other field loads; it is here only because that file was being
    edited by another agent when this was written (2026-10-01), and is to
    move there.  It is the one place outside [inv_raft_phys.v] that opens
    [own_raft_phys] -- through the file-local seal equation, by its
    qualified name -- and it does so for a single field load, re-sealing
    with the public [own_raft_phys_intro]. *)
Lemma wp_raft_load_pendingReadIndexMessages r id s :
  {{{ own_raft_phys cfg r id s }}}
    ![go.SliceType raftpb.Message] #(r.[raft.raft.t, "pendingReadIndexMessages"])
  {{{ (sl : slice.t), RET #sl; own_raft_phys cfg r id s ∗ ⌜ sl.(slice.len) = W64 0 ⌝ }}}.
Proof.
  iIntros (Φ) "H HΦ".
  iEval (rewrite inv_raft_phys.own_raft_phys_unseal) in "H". iNamed "H".
  iNamed "Hmisc".
  iDestruct (own_slice_len with "Hpri") as %[Hl Hl0].
  wp_apply (inv_raft_phys.wp_load_access with "Hr") as "Hr".
  iApply "HΦ". iSplitL; last (iPureIntro; simpl in Hl; word).
  iAssert (own_raft_misc rv.(raft.raft.readStates') rv.(raft.raft.readOnly')
             rv.(raft.raft.pendingReadIndexMessages'))
    with "[HreadStates HreadStates_cap Hro_obj Hpri Hpri_cap]" as "Hmisc".
  { rewrite /own_raft_misc. iFrame. }
  iApply (own_raft_phys_intro _ _ _ s with
    "Hr Hlogger Htrk Hlog Hmsgs Hmsgs_cap HmsgsAA HmsgsAA_cap Hmisc Houtbox");
    done.
Qed.

End helpers.

Set Default Proof Using "Type".

  (** The length test reads [0] and the function returns. *)
  Lemma wp_releasePendingReadIndexMessages :
    wp_releasePendingReadIndexMessages_body.
  Proof.
    intros_ambient.
    intros cfg r id s.
    wp_start as "Hphys". iNamed "Hphys".
    wp_auto.
    wp_apply (wp_raft_load_pendingReadIndexMessages with "Hphys")
      as "%sl [Hphys %Hsl]".
    rewrite Hsl.
    wp_auto.
    by iApply "HΦ".
  Qed.

End ReleasePendingReadIndexMessagesProof.

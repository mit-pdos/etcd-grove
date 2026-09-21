Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_raftLog__entries.

Module RaftLogEntriesProof (P : RAFTLOG__ENTRIES_POSTULATES) : RAFTLOG__ENTRIES.
Import P.

Section helper.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : raft.Assumptions}.
Collection W := sem + package_sem.
Set Default Proof Using "W".

(** [own_raftLog_at]'s no-wrap bound, read out without consuming the log.
    Needed to know [lastIndex() + 1] does not wrap, which is what makes the
    range premise of [raftLog.slice] hold. *)
Lemma raftLog_at_nowrap l prev sents uents :
  own_raftLog_at l prev sents uents -∗
  ⌜ (uint.Z prev.(raft.entryID.index') + Z.of_nat (length sents)
     + Z.of_nat (length uents) + 1 < 2^64)%Z ⌝ ∗
  own_raftLog_at l prev sents uents.
Proof.
  iIntros "H". iDestruct "H" as (lv) "H". iNamed "H".
  iAssert (own_raftLog_at l prev sents uents) with "[-]" as "Hlog".
  { rewrite /own_raftLog_at. iExists lv. iFrame "∗#%". }
  iSplitR "Hlog"; [ iPureIntro; exact Hnowrap | iExact "Hlog" ].
Qed.

End helper.

Set Default Proof Using "Type".

  Lemma wp_raftLog__entries_at : wp_raftLog__entries_at_body.
  Proof.
    intros_ambient.
    intros l prev sents uents i maxSize Hlo.
    wp_start as "H". iNamed "H". wp_auto.
    iDestruct (raftLog_at_nowrap with "Hlog") as "[%Hnw Hlog]".
    wp_apply (wp_raftLog__lastIndex_at with "[$Hlog]") as "%li [Hlog %Hli]".
    case_bool_decide as Hgt.
    - (* [i] is past the end: an empty page and no error.  The log is not
         opened at all, so [l ↦ lv] has to be split out of it by hand. *)
      wp_auto.
      iDestruct "Hlog" as (lv) "Hlog". iNamed "Hlog".
      iApply ("HΦ" $! slice.nil [] (DfracOwn 1) lv).
      iFrame "Hl". iSplitR; first iApply own_slice_nil.
      iIntros "Hl _". rewrite /own_raftLog_at. iExists lv. iFrame "∗#%".
    - wp_auto.
      wp_apply (wp_raftLog__lastIndex_at with "[$Hlog]") as "%li2 [Hlog %Hli2]".
      wp_apply (wp_raftLog__slice_at with "[$Hlog]")
        as "%sl %es %dq %lv (Hl & Hsl & %Hes & Hback)".
      { word. }
      try wp_auto.
      iApply ("HΦ" $! sl es dq lv). iFrame "Hl Hsl Hback".
  Qed.

End RaftLogEntriesProof.

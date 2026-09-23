Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raftLog__lastEntryID.

(** The indexed form, stated at a fixed split.  It is **internal**: the
    interface form in [spec_raftLog__lastEntryID.v] -- the one all four
    callers want -- is derived from it at the bottom of this file, and the
    ascription on the functor hides everything else, exactly as it hides
    [Step]'s branch lemmas.  So this is proof structure, not a second
    specification of [raftLog.lastEntryID]; see
    notes/false-statements.md for why the choice went this way here and the
    other way for [lastIndex]. *)
Definition wp_raftLog__lastEntryID_at_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (l : loc) prev sents uents,
  {{{ is_pkg_init raft ∗ "Hlog" ∷ own_raftLog_at l prev sents uents }}}
    l @! (go.PointerType raft.raftLog) @! "lastEntryID" #()
  {{{ (e : raft.entryID.t), RET #e; own_raftLog_at l prev sents uents }}}.

Module RaftLogLastEntryIDProof (P : RAFTLOG__LASTENTRYID_POSTULATES) : RAFTLOG__LASTENTRYID.
Import P.

  Lemma wp_raftLog__lastEntryID_at : wp_raftLog__lastEntryID_at_body.
  Proof.
    intros_ambient.
    intros l prev sents uents.
    wp_start as "H". iNamed "H". wp_auto.
    wp_apply (wp_raftLog__lastIndex_at with "[$Hlog]") as "%li [Hlog %Hli]".
    assert (Hb : (uint.Z prev.(raft.entryID.index') ≤ uint.Z li ≤
                  uint.Z prev.(raft.entryID.index') + Z.of_nat (length sents)
                  + Z.of_nat (length uents))%Z) by lia.
    (* [raftLog.term]'s triple is total ([spec_raftLog__term.v]); here the
       index is [lastIndex], so the in-range clause of its postcondition
       applies and the error is [nil] -- which is what makes the [Panicf]
       on the next line unreachable. *)
    wp_apply (wp_raftLog__term_at with "[$Hlog]") as "%t %err [Hlog %Herr]".
    apply (proj2 Herr) in Hb. subst err. wp_auto.
    iApply ("HΦ" $! (raft.entryID.mk t li)). iFrame.
  Qed.
  Arguments wp_raftLog__lastEntryID_at {_ _ _ _ _ _ _ _}.

  Lemma wp_raftLog__lastEntryID : wp_raftLog__lastEntryID_body.
  Proof.
    intros_ambient.
    intros l.

    iIntros (Φ) "[#Hinit Hlog] HΦ".
    iDestruct "Hlog" as (prev sents uents) "Hlog".
    wp_apply (wp_raftLog__lastEntryID_at with "[$Hlog]") as "%e Hlog".
    iApply "HΦ". iExists prev, sents, uents. iFrame.
  Qed.

End RaftLogLastEntryIDProof.

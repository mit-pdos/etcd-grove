Require Export New.proof.go_etcd_io.raft.election_proof.inv_raft_phys.

(** [logSliceFromMsgApp(m)] repackages an append message as a [logSlice]
    ([logSliceFromMsgAppⁱᵐᵖˡ], new/code/go_etcd_io/raft/v3.v:4866; raft.go):

        func logSliceFromMsgApp(m *pb.Message) logSlice {
          return logSlice{
            term:    m.Term,
            prev:    entryID{term: m.LogTerm, index: m.Index},
            entries: m.Entries,
          }
        }

    One exit, no panic, no call.  It takes a *pointer* ([handleAppendEntries]
    passes [&m]) and reads four fields; the [Entries] slice header is
    copied, not its contents, so nothing about the entries is owned or
    returned here. *)
Definition wp_logSliceFromMsgApp_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (p : loc) (dq : dfrac) (m : raftpb.Message.t),
  {{{ is_pkg_init raft ∗ p ↦{dq} m }}}
    @! raft.logSliceFromMsgApp #p
  {{{ RET #(raft.logSlice.mk m.(raftpb.Message.Term')
              (raft.entryID.mk m.(raftpb.Message.LogTerm') m.(raftpb.Message.Index'))
              m.(raftpb.Message.Entries'));
      p ↦{dq} m }}}.

Module Type LOGSLICEFROMMSGAPP.
  Parameter wp_logSliceFromMsgApp : wp_logSliceFromMsgApp_body.
  Arguments wp_logSliceFromMsgApp {_ _ _ _ _ _ _ _}.
End LOGSLICEFROMMSGAPP.

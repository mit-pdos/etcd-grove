(** * The raft log, opaque to election *)

Require Export New.proof.go_etcd_io.raft.v3_proof.election.defs.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : raft.Assumptions}.
Collection W := sem + package_sem.
Set Default Proof Using "W".

(** *** The log.

    Under our assumptions the only log operations on the election path are
    [lastEntryID] / [isUpToDate] (which can only make the node decline to
    vote, always protocol-legal), [lastIndex], and the single empty entry a
    new leader appends.  So the log is entirely opaque here. *)
Axiom own_raftLog : loc → iProp Σ.

Axiom wp_raftLog__lastEntryID : ∀ (l : loc),
  {{{ is_pkg_init raft ∗ own_raftLog l }}}
    l @! (go.PointerType raft.raftLog) @! "lastEntryID" #()
  {{{ (e : raft.entryID.t), RET #e; own_raftLog l }}}.

Axiom wp_raftLog__isUpToDate : ∀ (l : loc) (e : raft.entryID.t),
  {{{ is_pkg_init raft ∗ own_raftLog l }}}
    l @! (go.PointerType raft.raftLog) @! "isUpToDate" #e
  {{{ (b : bool), RET #b; own_raftLog l }}}.

Axiom wp_raftLog__lastIndex : ∀ (l : loc),
  {{{ is_pkg_init raft ∗ own_raftLog l }}}
    l @! (go.PointerType raft.raftLog) @! "lastIndex" #()
  {{{ (i : w64), RET #i; own_raftLog l }}}.

Axiom wp_raftLog__hasNextOrInProgressSnapshot : ∀ (l : loc),
  {{{ is_pkg_init raft ∗ own_raftLog l }}}
    l @! (go.PointerType raft.raftLog) @! "hasNextOrInProgressSnapshot" #()
  {{{ RET #false; own_raftLog l }}}.

End proof.

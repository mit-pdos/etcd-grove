(** * Raft components election neither reads nor writes

    Split out of [election.v] on 2026-09-14; see
    [notes/raft-election-refinement.md]. *)

Require Export New.proof.go_etcd_io.raft.v3_proof.election.inv_raftlog.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.inv_tracker.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : raft.Assumptions}.
Collection W := sem + package_sem.
Set Default Proof Using "W".

(** The (fixed) set of voters. *)
Context (cfg : gset w64).

(** [r.promotable()]: true exactly when this node is a voter.  It reads
    [r.id], [r.trk.Progress] and [r.raftLog], so it is stated against the
    raft struct rather than against three unrelated parameters. *)
Axiom wp_raft__promotable : ∀ (r : loc) rv votes,
  {{{ is_pkg_init raft ∗ r ↦ rv ∗
      own_tracker rv.(raft.raft.trk') votes ∗
      own_raftLog rv.(raft.raft.raftLog') }}}
    r @! (go.PointerType raft.raft) @! "promotable" #()
  {{{ (b : bool), RET #b;
      r ↦ rv ∗ own_tracker rv.(raft.raft.trk') votes ∗
      own_raftLog rv.(raft.raft.raftLog') ∗
      ⌜ b = bool_decide (rv.(raft.raft.id') ∈ cfg) ⌝ }}}.

(** [r.hasUnappliedConfChanges()]: false, since there is no
    reconfiguration. *)
Axiom wp_raft__hasUnappliedConfChanges : ∀ (r : loc) l,
  {{{ is_pkg_init raft ∗ own_raftLog l }}}
    r @! (go.PointerType raft.raft) @! "hasUnappliedConfChanges" #()
  {{{ RET #false; own_raftLog l }}}.

(** The ids of the voters, in some order, as [campaign] enumerates them.
    [campaign] calls this on [&r.trk.Config.Voters], so the receiver is that
    field ref and not the tracker itself. *)
Axiom wp_campaign_peer_ids : ∀ (trk : loc) tv votes,
  {{{ is_pkg_init quorum ∗ trk ↦ tv ∗ own_tracker tv votes }}}
    (trk.[tracker.ProgressTracker.t, "Config"].[tracker.Config.t, "Voters"])
      @! (go.PointerType quorum.JointConfig) @! "IDs" #()
  {{{ (mref : loc) (idm : gmap w64 unit), RET #mref;
      trk ↦ tv ∗ own_tracker tv votes ∗
      mref ↦$ idm ∗ ⌜ dom idm = cfg ⌝ }}}.

(** *** The parts of the raft struct election neither reads nor writes:
    the read-state slice, the read-only queue, and the pending
    [MsgReadIndex] slice.  Indexed by exactly those three fields, so that
    updating any other field of the struct leaves it alone. *)
Axiom own_raft_misc :
  ∀ (readStates : slice.t) (readOnly : loc) (pendingReadIndex : slice.t),
  iProp Σ.

Axiom wp_traceReceiveMessage : ∀ (r : loc) (mp : loc) rs ro pri,
  {{{ is_pkg_init raft ∗ own_raft_misc rs ro pri }}}
    @! raft.traceReceiveMessage #r #mp
  {{{ RET #(); own_raft_misc rs ro pri }}}.

Axiom wp_traceSendMessage : ∀ (r : loc) (mp : loc) rs ro pri,
  {{{ is_pkg_init raft ∗ own_raft_misc rs ro pri }}}
    @! raft.traceSendMessage #r #mp
  {{{ RET #(); own_raft_misc rs ro pri }}}.

Axiom wp_traceBecomeFollower : ∀ (r : loc) rs ro pri,
  {{{ is_pkg_init raft ∗ own_raft_misc rs ro pri }}}
    @! raft.traceBecomeFollower #r
  {{{ RET #(); own_raft_misc rs ro pri }}}.

Axiom wp_traceBecomeCandidate : ∀ (r : loc) rs ro pri,
  {{{ is_pkg_init raft ∗ own_raft_misc rs ro pri }}}
    @! raft.traceBecomeCandidate #r
  {{{ RET #(); own_raft_misc rs ro pri }}}.

Axiom wp_traceBecomeLeader : ∀ (r : loc) rs ro pri,
  {{{ is_pkg_init raft ∗ own_raft_misc rs ro pri }}}
    @! raft.traceBecomeLeader #r
  {{{ RET #(); own_raft_misc rs ro pri }}}.

(** The empty entry a new leader appends, and the append broadcast that
    follows it.  [bcastAppend] sends one [MsgApp] to each peer, which is
    exactly [step_win]'s [sent] list. *)
Axiom wp_raft__appendEmptyEntry : ∀ (r : loc) l (es : slice.t),
  {{{ is_pkg_init raft ∗ own_raftLog l }}}
    r @! (go.PointerType raft.raft) @! "appendEntry" #es
  {{{ RET #true; own_raftLog l }}}.

End proof.

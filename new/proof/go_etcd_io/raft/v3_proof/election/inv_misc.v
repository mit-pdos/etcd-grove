(** * Raft components election neither reads nor writes *)

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
      own_tracker cfg rv.(raft.raft.trk') votes ∗
      own_raftLog rv.(raft.raft.raftLog') }}}
    r @! (go.PointerType raft.raft) @! "promotable" #()
  {{{ (b : bool), RET #b;
      r ↦ rv ∗ own_tracker cfg rv.(raft.raft.trk') votes ∗
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
  {{{ is_pkg_init quorum ∗ trk ↦ tv ∗ own_tracker cfg tv votes }}}
    (trk.[tracker.ProgressTracker.t, "Config"].[tracker.Config.t, "Voters"])
      @! (go.PointerType quorum.JointConfig) @! "IDs" #()
  {{{ (mref : loc) (idm : gmap w64 unit), RET #mref;
      trk ↦ tv ∗ own_tracker cfg tv votes ∗
      mref ↦$ idm ∗ ⌜ dom idm = cfg ⌝ }}}.

(** *** The parts of the raft struct election neither reads nor writes:
    the read-state slice, the read-only queue, and the pending
    [MsgReadIndex] slice.  Indexed by exactly those three fields, so that
    updating any other field of the struct leaves it alone. *)
(** The five [traceX] functions below are **not** assumptions: Goose
    translates each of them to a literal no-op,
    [λ: <> <>, exception_do (do: #())], so each spec is a two-line proof.
    They were axioms until 2026-09-16 purely because nobody had looked at the
    generated body. *)

Axiom own_raft_misc :
  ∀ (readStates : slice.t) (readOnly : loc) (pendingReadIndex : slice.t),
  iProp Σ.

Lemma wp_traceReceiveMessage (r : loc) (mp : loc) rs ro pri :
  {{{ is_pkg_init raft ∗ own_raft_misc rs ro pri }}}
    @! raft.traceReceiveMessage #r #mp
  {{{ RET #(); own_raft_misc rs ro pri }}}.
Proof. wp_start as "Hm". by iApply "HΦ". Qed.

Lemma wp_traceSendMessage (r : loc) (mp : loc) rs ro pri :
  {{{ is_pkg_init raft ∗ own_raft_misc rs ro pri }}}
    @! raft.traceSendMessage #r #mp
  {{{ RET #(); own_raft_misc rs ro pri }}}.
Proof. wp_start as "Hm". by iApply "HΦ". Qed.

Lemma wp_traceBecomeFollower (r : loc) rs ro pri :
  {{{ is_pkg_init raft ∗ own_raft_misc rs ro pri }}}
    @! raft.traceBecomeFollower #r
  {{{ RET #(); own_raft_misc rs ro pri }}}.
Proof. wp_start as "Hm". by iApply "HΦ". Qed.

Lemma wp_traceBecomeCandidate (r : loc) rs ro pri :
  {{{ is_pkg_init raft ∗ own_raft_misc rs ro pri }}}
    @! raft.traceBecomeCandidate #r
  {{{ RET #(); own_raft_misc rs ro pri }}}.
Proof. wp_start as "Hm". by iApply "HΦ". Qed.

Lemma wp_traceBecomeLeader (r : loc) rs ro pri :
  {{{ is_pkg_init raft ∗ own_raft_misc rs ro pri }}}
    @! raft.traceBecomeLeader #r
  {{{ RET #(); own_raft_misc rs ro pri }}}.
Proof. wp_start as "Hm". by iApply "HΦ". Qed.

(** [reset] replaces [r.readOnly] with [newReadOnly(r.readOnly.option)].
    Two pieces are needed: reading the old object's [option] field, and
    installing the fresh object. *)
Lemma own_raft_misc_option rs ro pri :
  own_raft_misc rs ro pri -∗
  ∃ (o : raft.ReadOnlyOption.t),
    ro.[raft.readOnly.t, "option"] ↦ o ∗
    (ro.[raft.readOnly.t, "option"] ↦ o -∗ own_raft_misc rs ro pri).
Proof. Admitted.

(** The old queue is dropped and a fresh one installed.  The lemma *consumes*
    [own_raft_misc] at [ro] and returns it at [ro'], which is what [reset]
    does -- so this is not the discredited [own_raft_misc rv -∗
    own_raft_misc rv'] shape warned about above: it is tied to an actual
    allocation. *)
Lemma wp_newReadOnly (o : raft.ReadOnlyOption.t) rs ro pri :
  {{{ is_pkg_init raft ∗ own_raft_misc rs ro pri }}}
    @! raft.newReadOnly #o
  {{{ (ro' : loc), RET #ro'; own_raft_misc rs ro' pri }}}.
Proof. Admitted.

(** [resetRandomizedElectionTimeout] draws from the global RNG and writes
    [r.randomizedElectionTimeout].  The *RNG* is outside core raft and may be
    assumed; this wrapper is raft code, so it is a [Lemma].  The field it
    writes appears in no other conjunct of [own_raft_phys], and the model has
    no clock. *)
Lemma wp_raft__resetRandomizedElectionTimeout (r : loc) rv :
  {{{ is_pkg_init raft ∗ r ↦ rv }}}
    r @! (go.PointerType raft.raft) @! "resetRandomizedElectionTimeout" #()
  {{{ (n : w64), RET #();
      r ↦ (rv <| raft.raft.randomizedElectionTimeout' := n |>) }}}.
Proof. Admitted.

(** [abortLeaderTransfer] clears [leadTransferee], which [own_raft_phys]
    requires to be zero anyway. *)
Lemma wp_raft__abortLeaderTransfer (r : loc) rv :
  {{{ is_pkg_init raft ∗ r ↦ rv }}}
    r @! (go.PointerType raft.raft) @! "abortLeaderTransfer" #()
  {{{ RET #(); r ↦ (rv <| raft.raft.leadTransferee' := W64 0 |>) }}}.
Proof. Admitted.

(** [wp_raft__appendEmptyEntry] used to live here.  It moved to
    [inv_raft_phys.v], because stating it honestly needs [own_raft_phys]:
    [appendEntry] queues a [MsgAppResp], so an axiom owning only the log is
    false. *)

End proof.

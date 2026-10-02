Require Export New.code.go_etcd_io.raft.v3.
Require Export New.generatedproof.go_etcd_io.raft.v3.
Require Export New.proof.proof_prelude.
From New.proof Require Export context sync fmt slices cmp encoding.binary.

Section init.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : raft.Assumptions}.
Collection W := sem + package_sem.
Set Default Proof Using "W".

#[global] Instance : IsPkgInit (iProp Σ) raftpb := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) raftpb := build_get_is_pkg_init_wf.

#[global] Instance : IsPkgInit (iProp Σ) strconv := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) strconv := build_get_is_pkg_init_wf.

#[global] Instance : IsPkgInit (iProp Σ) strings := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) strings := build_get_is_pkg_init_wf.

#[global] Instance : IsPkgInit (iProp Σ) math := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) math := build_get_is_pkg_init_wf.

#[global] Instance : IsPkgInit (iProp Σ) quorum := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) quorum := build_get_is_pkg_init_wf.

#[global] Instance : IsPkgInit (iProp Σ) tracker := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) tracker := build_get_is_pkg_init_wf.

#[global] Instance : IsPkgInit (iProp Σ) confchange := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) confchange := build_get_is_pkg_init_wf.

#[global] Instance : IsPkgInit (iProp Σ) big := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) big := build_get_is_pkg_init_wf.

(** [crypto/rand]'s package-level [Reader] (an [io.Reader]).  [lockedRand.Intn]
    reads it through [GlobalVarAddr] to pass it to [rand.Int], so a proof of
    that method needs the points-to.  Its value is opaque: nothing is known
    about it beyond being the reader the package installed, and the
    [rand.Int] triple ([spec_rand_Int.v]) is stated for exactly that
    reader.  Like everything else in this file, an assumption about
    initialisation: nothing here proves it from [rand.initialize']
    (whose body, [Reader'init], Goose leaves as an [Axiom]). *)
Definition is_rand_initialized : iProp Σ :=
  ∃ (rdr : interface.t),
    "#Reader" ∷ (global_addr rand.Reader) ↦□ rdr.

#[global] Instance : IsPkgInit (iProp Σ) rand := define_is_pkg_init is_rand_initialized.
#[global] Instance : GetIsPkgInitWf (iProp Σ) rand := build_get_is_pkg_init_wf.

#[global] Instance : IsPkgInit (iProp Σ) bytes := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) bytes := build_get_is_pkg_init_wf.

#[global] Instance : IsPkgInit (iProp Σ) os := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) os := build_get_is_pkg_init_wf.

#[global] Instance : IsPkgInit (iProp Σ) log := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) log := build_get_is_pkg_init_wf.

#[global] Instance : IsPkgInit (iProp Σ) io := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) io := build_get_is_pkg_init_wf.

#[global] Instance : IsPkgInit (iProp Σ) errors := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) errors := build_get_is_pkg_init_wf.

(** The package-level [error] variables the election path compares against.
    Each is a non-nil interface value installed by the package initializer;
    a proof that reads one needs the points-to (the load is through
    [GlobalVarAddr]) and the disequality (to decide [err == ErrX] when [err]
    is [nil]).  [ErrCompacted]/[ErrUnavailable] are read by [raftLog.slice]
    after [Storage.Entries] (added 2026-09-19 for
    [hasUnappliedConfChanges]). *)
(** [globalRand] is the package-level [*lockedRand] behind
    [raft.resetRandomizedElectionTimeout].  Its one field, [mu], is a
    [sync.Mutex] that guards nothing the proof can see ([Intn] holds it
    across a [crypto/rand] call, whose only state is the kernel's), so the
    lock invariant is [True].  The package initializer installs
    [&lockedRand{}] (a zero [Mutex]), which is exactly what [init_Mutex]
    turns into [is_Mutex … True]. *)
Definition is_lockedRand (lr : loc) : iProp Σ :=
  "#Hmu" ∷ is_Mutex (lr.[raft.lockedRand.t, "mu"]) True.

(** An [error] value shaped the way [errors.New] builds one: an interface
    holding a **pointer**.

    Why this is needed, and why it is not decoration.  Go's interface
    equality is not a [bool_decide]: [new/golang/defn/interface.v]'s
    [go_eq_interface] reduces [i1 == i2] for two non-[nil] values to

      if decide (i1.ty = i2.ty)
      then CheckComparable i1.ty ;; GoOp GoEquals i1.ty (i1.v, i2.v)
      else #false

    and [CheckComparable t] has a reduction only for the types Goose knows
    to be comparable.  For an *unknown* dynamic type there is none, so a
    proof that reaches [err == ErrX] with [err] non-[nil] is **stuck** -- it
    cannot even step, let alone decide the branch.  That is exactly what
    [raft.maybeSendSnapshot] does with
    [ErrSnapshotTemporarilyUnavailable] (new/code/go_etcd_io/raft/v3.v:3188).
    [proof_raftLog__slice.v] compares against [ErrCompacted] and
    [ErrUnavailable] and does *not* need this, only because there [err] is
    [interface.nil] and the [nil]/[ok] case of [go_eq_interface] answers
    [false] outright.

    The claim is true of the value the package initializer installs:
    [errors.New] ([new/code/errors.v:48]) returns
    [Convert (go.PointerType errorString) go.error (GoAlloc errorString …)],
    and [convert_to_interface] turns that into
    [interface.mk_ok (go.PointerType errors.errorString) #p].  The type is
    left existential here rather than pinned to [errors.errorString],
    because all the comparison needs is that it is *a* pointer type:
    [check_comparable_pointer] ([new/golang/defn/postlang.v]) fires for
    every [go.PointerType], and [go_eq_pointer] then makes the comparison
    [bool_decide (p1 = p2)].

    Added 2026-09-21 for [wp_raft__maybeSendSnapshot]. *)
Definition is_new_error (e : interface.t) : Prop :=
  ∃ (t : go.type) (p : loc), e = interface.mk_ok (go.PointerType t) #p.

Definition is_initialized : iProp Σ :=
  ∃ errStopped errCompacted errUnavailable errSnapUnavail errPropDropped (globalRand : loc),
    "ErrStopped" ∷ (global_addr raft.ErrStopped) ↦□ errStopped ∗
    "%HErrStopped" ∷ ⌜ errStopped ≠ interface.nil ⌝ ∗
    (** [maybeSendSnapshot] compares [Storage.Snapshot]'s error against this
        one; it is the only non-fatal error that method may return, and
        [is_Storage]'s [HSnapshot] triple ([inv_storage.v]) is stated in
        terms of it.  Added 2026-09-20 for [bcastAppend]. *)
    "ErrSnapUnavail" ∷
        (global_addr raft.ErrSnapshotTemporarilyUnavailable) ↦□ errSnapUnavail ∗
    "%HErrSnapUnavail" ∷ ⌜ errSnapUnavail ≠ interface.nil ⌝ ∗
    (** and, unlike the other three, [maybeSendSnapshot] *compares* a
        non-[nil] error against it, which needs the dynamic type to be
        comparable -- see [is_new_error] above. *)
    "%HErrSnapUnavail_new" ∷ ⌜ is_new_error errSnapUnavail ⌝ ∗
    "ErrCompacted" ∷ (global_addr raft.ErrCompacted) ↦□ errCompacted ∗
    "%HErrCompacted" ∷ ⌜ errCompacted ≠ interface.nil ⌝ ∗
    "ErrUnavailable" ∷ (global_addr raft.ErrUnavailable) ↦□ errUnavailable ∗
    "%HErrUnavailable" ∷ ⌜ errUnavailable ≠ interface.nil ⌝ ∗
    (** [raftLog.zeroTermOnOutOfBounds] compares a non-[nil] error (what
        [raftLog.term] returned) against both, which needs their dynamic
        types to be comparable -- [is_new_error] above.  Both are
        [errors.New(...)] in [storage.go].  Added 2026-10-01 for
        [handleAppendEntries]'s reject path. *)
    "%HErrCompacted_new" ∷ ⌜ is_new_error errCompacted ⌝ ∗
    "%HErrUnavailable_new" ∷ ⌜ is_new_error errUnavailable ⌝ ∗
    (** [ErrProposalDropped = errors.New("raft proposal dropped")]
        ([raft.go]), which [stepFollower]/[stepCandidate] return for a
        proposal they cannot forward.  Only loaded and returned, never
        compared, so no [is_new_error].  Added 2026-10-01. *)
    "ErrPropDropped" ∷ (global_addr raft.ErrProposalDropped) ↦□ errPropDropped ∗
    "%HErrPropDropped" ∷ ⌜ errPropDropped ≠ interface.nil ⌝ ∗
    (** the global RNG: the pointer, and the mutex behind it (added
        2026-09-20 for [resetRandomizedElectionTimeout]) *)
    "#globalRand" ∷ (global_addr raft.globalRand) ↦□ globalRand ∗
    "#HglobalRand" ∷ is_lockedRand globalRand ∗
    (** [emptyState = pb.HardState{}] ([node.go]), which [IsEmptyHardState]
        compares against.  Nothing but the initializer writes it.  Added
        2026-09-24 for [newRaft]. *)
    "#emptyState" ∷ (global_addr raft.emptyState)
                      ↦□ raftpb.HardState.mk (W64 0) (W64 0) (W64 0).

#[global] Instance : IsPkgInit (iProp Σ) raft := define_is_pkg_init is_initialized.
#[global] Instance : GetIsPkgInitWf (iProp Σ) raft := build_get_is_pkg_init_wf.

End init.

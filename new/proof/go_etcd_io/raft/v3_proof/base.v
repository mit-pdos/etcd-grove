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

Definition is_initialized : iProp Σ :=
  ∃ errStopped errCompacted errUnavailable errSnapUnavail (globalRand : loc),
    "ErrStopped" ∷ (global_addr raft.ErrStopped) ↦□ errStopped ∗
    "%HErrStopped" ∷ ⌜ errStopped ≠ interface.nil ⌝ ∗
    (** [maybeSendSnapshot] compares [Storage.Snapshot]'s error against this
        one; it is the only non-fatal error that method may return, and
        [is_Storage]'s [HSnapshot] triple ([inv_storage.v]) is stated in
        terms of it.  Added 2026-09-20 for [bcastAppend]. *)
    "ErrSnapUnavail" ∷
        (global_addr raft.ErrSnapshotTemporarilyUnavailable) ↦□ errSnapUnavail ∗
    "%HErrSnapUnavail" ∷ ⌜ errSnapUnavail ≠ interface.nil ⌝ ∗
    "ErrCompacted" ∷ (global_addr raft.ErrCompacted) ↦□ errCompacted ∗
    "%HErrCompacted" ∷ ⌜ errCompacted ≠ interface.nil ⌝ ∗
    "ErrUnavailable" ∷ (global_addr raft.ErrUnavailable) ↦□ errUnavailable ∗
    "%HErrUnavailable" ∷ ⌜ errUnavailable ≠ interface.nil ⌝ ∗
    (** the global RNG: the pointer, and the mutex behind it (added
        2026-09-20 for [resetRandomizedElectionTimeout]) *)
    "#globalRand" ∷ (global_addr raft.globalRand) ↦□ globalRand ∗
    "#HglobalRand" ∷ is_lockedRand globalRand.

#[global] Instance : IsPkgInit (iProp Σ) raft := define_is_pkg_init is_initialized.
#[global] Instance : GetIsPkgInitWf (iProp Σ) raft := build_get_is_pkg_init_wf.

End init.

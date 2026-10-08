/-
Port of `election_proof/spec_raft__hasUnappliedConfChanges.v` (feb5c73d4).

Lean notes: `None` is `none`.
-/
module

public import Proof.go_etcd_io.raft.v3.InvRaftPhys

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `r.hasUnappliedConfChanges()`: false, since there is no reconfiguration.

The tempting shortcut does not work: the generated body (Rocq
new/code/go_etcd_io/raft/v3.v:3732; `raft.hasUnappliedConfChanges.impl` in
`Code/go_etcd_io/raft/v3.lean`) opens with

    if r.raftLog.applied >= r.raftLog.committed { return false }

but `applied >= committed` is a fact about the log that nothing available implies, so
the `scan` over `(applied, committed]` is **genuinely reachable** -- it is not dead
under our scope. Returning `false` therefore needs `ownRaftLog` to say that no entry in
that range has `Type` `EntryConfChange` or `EntryConfChangeV2`, which is
`HnoConfChange` in `ownRaftLog` (`InvRaftlog.lean`), together with
`Happlied`/`Hcommitted` placing `(applied, committed]` inside the log so that `scan`'s
bounds checks cannot panic.

**Owns the receiver.** The method has a pointer receiver and reads `r.raftLog` through
it four times before anything else, so the triple takes `r ↦ rv` and speaks of
`ownRaftLog rv.raftLog'` -- the `tracker.ProgressTracker.Visit.spec` rule (main's
notes/false-statements.md). Until 2026-09-19 it was stated on an unrelated `l : Loc`
with no ownership of `r` at all, which asserted the safety of a load it did not own;
that version was never proved. `r.logger` is also read, but only on the `Panicf` path,
which is dead. -/
abbrev raft.hasUnappliedConfChanges.spec : Prop :=
  ∀ (cfg : GSet w64) (r : Loc) (id : w64) (s : NState),
  -- no snapshot pending: `applied` is then at or above the compaction boundary, so
  -- `scan`'s range starts inside the log. With one pending `applied` may lie below the
  -- snapshot's index and `scan` would return `ErrCompacted` into the `Panicf` -- the
  -- reason `hup` tests `promotable` (which checks `hasNextOrInProgressSnapshot`)
  -- first. Added 2026-10-02.
  s.logst.snap = none →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ ownRaftPhys cfg r id s }}
    (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"hasUnappliedConfChanges"))
      (Val #()))
  {{ RET #false; ownRaftPhys cfg r id s }}

end spec

end EtcdGrove
end Perennial

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

/-- `r.hasUnappliedConfChanges()`: whether a committed entry not applied yet (at
`(applied, committed]`, `unappliedEnts`) is a configuration change (`IsConfEnt`).

(Until 2026-10-13: always `false`, from `ownRaftLog`'s `HnoConfChange`, the scope
assumption that no configuration change is ever requested. Reconfiguration stage D lets
conf-change entries into the log, and this is the real answer.)

The generated body opens with `if r.raftLog.applied >= r.raftLog.committed { return
false }` (the range is then empty); otherwise it `scan`s the range, its callback setting
`found` and stopping the scan with `errBreak` at the first conf-change entry, and
`Panicf`s on any other error (dead: `scan`'s only errors are the callback's).

**Owns the receiver.** The method has a pointer receiver and reads `r.raftLog` through
it four times before anything else, so the triple takes `ownRaftPhys` (until 2026-09-19
it was stated on an unrelated `l : Loc` with no ownership of `r` at all; main's
notes/false-statements.md). `r.logger` is also read, but only on the `Panicf` path,
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
  {{ (b : Bool), RET #b; ownRaftPhys cfg r id s ∗
      ⌜b = true ↔ ∃ e ∈ unappliedEnts s.logst, IsConfEnt e⌝ }}

end spec

end EtcdGrove
end Perennial

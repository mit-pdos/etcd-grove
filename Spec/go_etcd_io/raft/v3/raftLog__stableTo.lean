/-
Port of `election_proof/spec_raftLog__stableTo.v` (857d09190).
-/
module

public import Proof.go_etcd_io.raft.v3.InvReadylog

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `l.stableTo(id)` (`log.go:365`) is `l.unstable.stableTo(id)`: on a hit
(`StableHit`, `InvReadylog.lean`) the entries up to `id` move from the unstable suffix
to the stable part (`logStableTo`); the protocol log `sents ++ uents` does not change.

The premise `StableOk` is what keeps `ownRaftLog`'s storage relation: the entries moved
stable are persisted (nothing left unpersisted, and the storage holds the log up to
`id`: `stored`; until 2026-10-10 `id.index < offsetInProgress`) and no snapshot is
pending. Go checks only the term at `id.index`, so this is a real premise -- see
`StableOk`.

(D22 S-d1b, 2026-10-21) On `ownRaftLogW`: the acknowledgement of a snapshot's `Ready` moves the
entries after the snapshot stable while the snapshot is still pending, in the `sapp` window (the
storage holds the snapshot and those entries); `StableOk` admits that window for a hit. A caller
outside it converts (`ownRaftLog_toW`, `ownRaftLogW_quiet`: `logStableTo` keeps both windows'
flags). -/
abbrev raftLog.stableTo.spec : Prop :=
  ∀ (l : Loc) (ls : LogState) (id : entryID),
  StableOk ls id →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ "Hlog" ∷ ownRaftLogW l ls }}
    (App (Val (l @!! go.GoType.PointerType raftLog.ty @!! go!"stableTo")) (Val #id))
  {{ RET #(); ownRaftLogW l (logStableTo ls id) }}

end spec

end EtcdGrove
end Perennial

/-
Port of `election_proof/spec_raftLog__stableTo.v` (857d09190).
-/
import EtcdGrove.Raft.InvReadylog

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

/-- `l.stableTo(id)` (`log.go:365`) is `l.unstable.stableTo(id)`: on a hit
(`StableHit`, `InvReadylog.lean`) the entries up to `id` move from the unstable suffix
to the stable part (`logStableTo`); the protocol log `sents ++ uents` does not change.

The premise `StableOk` is what keeps `ownRaftLog`'s storage relation: the entries moved
stable are persisted (in progress, nothing left unpersisted) and no snapshot is
pending. Go checks only the term at `id.index`, so this is a real premise -- see
`StableOk`. -/
abbrev raftLog.stableTo.spec : Prop :=
  ∀ (l : Loc) (ls : LogState) (id : entryID),
  StableOk ls id →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ "Hlog" ∷ ownRaftLog l ls }}
    (App (Val (l @!! go.GoType.PointerType raftLog.ty @!! go!"stableTo")) (Val #id))
  {{ RET #(); ownRaftLog l (logStableTo ls id) }}

end spec

end EtcdGrove
end Perennial

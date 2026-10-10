/-
Port of `election_proof/spec_raftLog__acceptUnstable.v` (857d09190).
-/
module

public import Proof.go_etcd_io.raft.v3.InvReadylog

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

/-- `l.acceptUnstable()` (`log.go:373`) is `l.unstable.acceptInProgress()`: every
unstable entry is now in progress (`offsetInProgress` at the end of the log), and the
entries the `Ready` just handed out (`nextUnstable`) become the application's to persist
(`LogState.unpersisted`, `logAcceptUnstable`, `InvReadylog.lean`). The premise is that
the previous `Ready`'s entries were appended: the log records one batch of unpersisted
entries at a time, and `Advance` -- which a `Ready` must follow -- needs them appended
anyway.

Since 2026-10-10 the storage's hand-out -- the right to append the batch -- is a separate
ghost step before the call (`ownRaftLog_handout`, `InvReadylog.lean`): the log comes in at
`logHanded ls`, the batch already recorded as unpersisted. `node.go` hands the right to the
application before `run` calls `acceptReady`. -/
abbrev raftLog.acceptUnstable.spec : Prop :=
  ∀ (l : Loc) (ls : LogState),
  ls.unpersisted = [] →
  ls.snap = none →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hlog" ∷ ownRaftLog l (logHanded ls) }}
    (App (Val (l @!! go.GoType.PointerType raftLog.ty @!! go!"acceptUnstable")) (Val #()))
  {{ RET #(); ownRaftLog l (logAcceptUnstable ls) }}

end spec

end EtcdGrove
end Perennial

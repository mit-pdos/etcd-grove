/-
Port of `election_proof/spec_raftLog__nextCommittedEnts.v` (857d09190).
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

/-- `l.nextCommittedEnts(allowUnstable)` (`log.go:218`):

    if l.applyingEntsPaused { return nil }
    if l.hasNextOrInProgressSnapshot() { return nil }
    lo, hi := l.applying+1, l.maxAppliableIndex(allowUnstable)+1
    if lo >= hi { return nil }
    maxSize := l.maxApplyingEntsSize - l.applyingEntsSize
    if maxSize <= 0 { l.logger.Panicf(...) }
    ents, err := l.slice(lo, hi, maxSize)
    if err != nil { l.logger.Panicf(...) }
    return ents

The committed entries after `applying`, cut short by `maxSize` -- a prefix of
`logCommittedEnts` (`InvReadylog.lean`), possibly empty (paused, a pending snapshot,
nothing to apply). Read-only, with the slice's capacity (`raftLog.slice`'s result is
capped). Neither `Panicf` is reachable: `ownRaftLog`'s `Hpaused` leaves room under the
limit while applying is not paused, and `slice` does not fail. -/
abbrev raftLog.nextCommittedEnts.spec : Prop :=
  ∀ (l : Loc) (ls : LogState) (au : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ "Hlog" ∷ ownRaftLog l ls }}
    (App (Val (l @!! go.GoType.PointerType raftLog.ty @!! go!"nextCommittedEnts"))
      (Val #au))
  {{ (s : GoSlice) (ce : List raftpb.Entry), RET #s;
      ownRaftLog l ls ∗ s ↦*□ ce ∗ ownSliceCap raftpb.Entry s (DFrac.own 1) ∗
      ⌜ce <+: logCommittedEnts ls ∧ (ls.snap ≠ none → ce = [])⌝ }}

end spec

end EtcdGrove
end Perennial

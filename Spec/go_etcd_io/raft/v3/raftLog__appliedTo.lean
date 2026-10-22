/- Port of election_proof/spec_raftLog__appliedTo.v (857d09190). -/
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

/-- `l.appliedTo(i, size)` advances `applied` to `i`, and `applying` to
`max(applying, i)` (since 2026-10-05, when `applying` joined `LogState` for `Ready`),
and releases `size` of `applyingEntsSize` (saturating at `0`). It `Panicf`s unless
`applied ≤ i ≤ committed`, hence the premise; `applyingEntsPaused` (also written) is
not part of `LogState`.

(D22 S-d1b, 2026-10-21) On `ownRaftLogW`: `raft.appliedSnap` calls it (through `raft.appliedTo`)
in its window (`aps`: `stableSnapTo` dropped the snapshot, `applied` below the boundary), which
ends once `i` reaches the boundary. -/
abbrev raftLog.appliedTo.spec : Prop :=
  ∀ (l : Loc) (ls : LogState) (i size : w64),
  uint.Z ls.applied ≤ uint.Z i ∧ uint.Z i ≤ uint.Z ls.committed →
  -- (D19i part 1) past `applying` only below `offsetInProgress` (`ownRaftLog`'s `FlOk`; D22
  -- S-d1b: with a snapshot pending too)
  (uint.Z ls.applying < uint.Z i → uint.Z i < uint.Z ls.inprogress) →
  -- (D22 S-d4 item 3) with a snapshot pending and the storage not lent, past `applying` only up to
  -- what the storage holds (`LogState.sxt`, `StorExtOk`)
  (ls.snap ≠ none → ls.lent = false → uint.Z ls.applying < uint.Z i → uint.Z i ≤ uint.Z ls.sxt) →
  -- (D22 S-r, 2026-10-21) and, with a pending snapshot not yet handed out, below its index
  -- (`SipOk`: `applying` stays below it until a `Ready` hands it out)
  (ls.snap ≠ none → ls.sip = false → uint.Z ls.applying < uint.Z i →
    uint.Z i < uint.Z ls.prev.index') →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ ownRaftLogW l ls }}
    (App (App (Val (l @!! go.GoType.PointerType raftLog.ty @!! go!"appliedTo")) (Val #i))
      (Val #size))
  {{ RET #(); ownRaftLogW l
      { ls with
          applied := i,
          applying := w64Max ls.applying i,
          apsize := if uint.Z size < uint.Z ls.apsize then ls.apsize - size else W64 0,
          aps := ls.aps && decide (uint.Z i < uint.Z ls.prev.index') } }}

end spec

end EtcdGrove
end Perennial

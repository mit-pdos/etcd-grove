/-
Port of `election_proof/spec_raftLog__acceptApplying.v` (857d09190).
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

/-- `l.acceptApplying(i, size, allowUnstable)` (`log.go:345`): the entries up to `i`
have been handed out for applying.

    if l.committed < i { l.logger.Panicf(...) }
    l.applying = i
    l.applyingEntsSize += size
    l.applyingEntsPaused = l.applyingEntsSize >= l.maxApplyingEntsSize ||
        i < l.maxAppliableIndex(allowUnstable)

`applying` becomes `i` and `applyingEntsSize` grows by `size` (a `uint64` sum, as Go
computes it); the paused flag is internal. The premise is the `Panicf`'s guard and,
below, what keeps `applied <= applying` (`acceptReady` passes the last committed entry
handed out, above `applying`). -/
abbrev raftLog.acceptApplying.spec : Prop :=
  ∀ (l : Loc) (ls : LogState) (i size : w64) (au : Bool),
  uint.Z ls.applied ≤ uint.Z i ∧ uint.Z i ≤ uint.Z ls.committed ∧
  -- (D19i part 1) `applying` does not move back (the floor is at most it), and stays below
  -- `offsetInProgress` (`FlOk`: `acceptReady` accepts the unstable entries first)
  -- (D22 S-d1b, 2026-10-21: with a snapshot pending too)
  uint.Z ls.applying ≤ uint.Z i ∧ uint.Z i < uint.Z ls.inprogress →
  -- (D22 S-d4 item 3) with a snapshot pending nothing is handed out for applying (`acceptReady`:
  -- `nextCommittedEnts` is empty then), so `applying` stays within what the storage holds
  (ls.snap ≠ none → uint.Z i ≤ uint.Z ls.applying) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ "Hlog" ∷ ownRaftLog l ls }}
    (App (App (App (Val (l @!! go.GoType.PointerType raftLog.ty @!! go!"acceptApplying"))
      (Val #i)) (Val #size)) (Val #au))
  {{ RET #(); ownRaftLog l { ls with applying := i, apsize := ls.apsize + size } }}

end spec

end EtcdGrove
end Perennial

/-
Lean-first (no Rocq counterpart).

# The statistics' counters (2026-10-29, track C)

`Stats` (cluster.go) counts what a run exercised, for the tests; the store never reads it. Every
counter is an `atomic.Uint64` that any goroutine adds to (`Stats.add`), so each is in an invariant of
its own holding the whole `ownUint64` at some value (`isCounter`); `isStats s` is every counter of
the `Stats` at `s`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.kvreconf.Base
public import Perennial.Proof.sync.atomic.Base

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvreconf

open Iris Iris.BI go_etcd_io.raft.v3

/-- The namespace of the statistics' counters. -/
def kvrStatsN : Namespace := nroot.@"kvreconf_stats"

/-- The store's statistics struct. -/
abbrev RStats [GooseExts] := github_com.mit_pdos.etcd_grove.examples.kvreconf.Stats

/-- The names of `Stats`' counters. -/
def statsFields : List GoString :=
  [go!"SnapshotsTaken", go!"SnapshotsTakenJoint", go!"SnapshotsSent", go!"SnapshotsInstalled",
   go!"SnapshotsInstalledJoint", go!"SnapshotsInstalledLearners", go!"Compactions",
   go!"ConfChangesProposed", go!"ConfChangesApplied", go!"ConfChangesRejected", go!"JointEntered",
   go!"ReplicasStarted", go!"Dropped", go!"Duplicated", go!"Delayed", go!"Retries"]

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- A counter any goroutine adds to (see the file header). -/
def isCounter (c : Loc) : IProp GF :=
  inv kvrStatsN iprop(∃ v : w64, sync.atomic.ownUint64 c (DFrac.own 1) v)

instance isCounter_persistent (c : Loc) : Persistent (isCounter (GF := GF) c) := by
  unfold isCounter; infer_instance

/-- Every counter of the `Stats` at `s`. -/
def isStats (s : Loc) : IProp GF :=
  [∗list] f ∈ statsFields, isCounter (s.[RStats, f])

instance isStats_persistent (s : Loc) : Persistent (isStats (GF := GF) s) := by
  unfold isStats; infer_instance

/-- One counter of `isStats`. -/
theorem isStats_field (s : Loc) (f : GoString) (hf : f ∈ statsFields) :
    isStats (GF := GF) s ⊢ isCounter (s.[RStats, f]) := by
  unfold isStats
  exact BigSepL.bigSepL_mem hf

end defs

end kvreconf
end EtcdGrove
end Perennial

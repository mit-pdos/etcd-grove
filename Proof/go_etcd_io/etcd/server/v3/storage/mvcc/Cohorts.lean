/-
`syncWatchers`' cohorts (etcd-io/etcd#22304, `watchable_store.go`: `revCohort`,
`cohortsByRevision`). Lean-first (no Rocq counterpart); see `notes/pr-verify/etcd-22304.md`.

`cohortsByRevision(wg, compactionRev)` groups the members of `wg` not behind the compaction
revision into cohorts, in increasing `minRev` order: a cohort starts at the least `minRev` not
yet grouped and takes every member within `watchBatchMaxRevs` of it. `syncWatchers` then scans
each cohort's revisions from its start, so a member's events from its own `minRev` are in its
cohort's scan only because the cohort's start is at or below every member's `minRev`
(`CohortsOk.window`), which holds because the members are sorted before grouping.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvWatchBatch

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc

/-- A cohort: the revision its scan starts at, its group (a fresh one), the group's members. -/
structure Cohort where
  minRev : w64
  wg : Loc
  W : GMap Loc WatchRange

section val
variable [ext : FfiSyntax] [go_gctx : GoGlobalContext]

/-- The `revCohort` value of a cohort. -/
def Cohort.val (c : Cohort) : revCohort := { minRev' := c.minRev, wg' := c.wg }

end val

/-- `cohortsByRevision`'s result `L` for the members `W` (states `ST`), the compaction revision
`cr` and the window `n` (`watchBatchMaxRevs`):
- the cohorts' members are members of `W`, no member in two cohorts, and every member at or
  above `cr` is in one;
- each cohort is not empty, its members at or above `cr`, within `[minRev, minRev + n]` of its
  start, which is one of its members' `minRev`;
- the cohorts are in increasing order, more than `n` apart. -/
structure CohortsOk (W : GMap Loc WatchRange) (ST : GMap Loc WatcherSt) (cr n : Int)
    (L : List Cohort) : Prop where
  sub : ∀ c ∈ L, ∀ w r, c.W !! w = some r → W !! w = some r
  disj : L.Pairwise (fun c d => ∀ w, (c.W !! w).isSome → d.W !! w = none)
  cover : ∀ w r st, W !! w = some r → ST !! w = some st → cr ≤ sint.Z st.minRev →
    ∃ c ∈ L, (c.W !! w).isSome
  live : ∀ c ∈ L, ∀ w st, (c.W !! w).isSome → ST !! w = some st → cr ≤ sint.Z st.minRev
  window : ∀ c ∈ L, ∀ w st, (c.W !! w).isSome → ST !! w = some st →
    sint.Z c.minRev ≤ sint.Z st.minRev ∧ sint.Z st.minRev ≤ sint.Z c.minRev + n
  anchor : ∀ c ∈ L, ∃ w st, (c.W !! w).isSome ∧ ST !! w = some st ∧ st.minRev = c.minRev
  sorted : L.Pairwise (fun c d => sint.Z c.minRev + n < sint.Z d.minRev)

end mvcc
end EtcdGrove
end Perennial

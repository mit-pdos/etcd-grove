/-
`cohortsByRevision` (`watchable_store.go`, etcd-io/etcd#22304). Lean-first (no Rocq
counterpart); see `Cohorts.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Cohorts

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- `cohortsByRevision(wg, compactionRev)` of a group with members `W` (states `ST`, their
`minRev`s not negative): the cohorts of `W`'s members at or above `compactionRev`, in a slice of
`revCohort`s, each with a fresh group of its members (`CohortsOk`, for the window
`watchBatchMaxRevs` = `1000`); the group and the states are given back unchanged. -/
abbrev mvcc.cohortsByRevision.spec : Prop :=
  ∀ (wg : Loc) (W : GMap Loc mvcc.WatchRange) (ST : GMap Loc mvcc.WatcherSt) (compactRev : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.ownWatcherGroup wg W ∗ mvcc.ownStates ST ∗
      ⌜(∀ w, (W !! w).isSome → (ST !! w).isSome) ∧
        (∀ w st, (W !! w).isSome → ST !! w = some st → 0 ≤ sint.Z st.minRev) ∧
        GMap.size W < 2 ^ 62⌝ }}
    (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.mvcc.cohortsByRevision)) (Val #wg))
      (Val #compactRev))
  {{ (cs : GoSlice), RET #cs; ∃ L : List mvcc.Cohort,
      mvcc.ownWatcherGroup wg W ∗ mvcc.ownStates ST ∗ cs ↦* (L.map mvcc.Cohort.val) ∗
      ([∗list] c ∈ L, mvcc.ownWatcherGroup c.wg c.W) ∗
      ⌜mvcc.CohortsOk W ST (sint.Z compactRev) 1000 L⌝ }}

end spec

end EtcdGrove
end Perennial

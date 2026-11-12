/-
## `raft.hasUnappliedConfChanges` (internal)

`hup`. Mirrors the code: R3's `scan` of `(applied, committed]` (held by the storage or the unstable log: the compaction point is at most the applied index), paginated; no panic. **Changes.** Over the opened struct (internal layer, `ApiCore.lean`; from `specs-ref`'s
`raft__hasUnappliedConfChanges.lean`, over `NState`); round 1: the result is stated over the state. Verify-round (A4 P3): the premise that no floor is published above `applied` (`hup` has it from `coreIdle_floor`); the scan from `applied + 1` then meets no compaction. `errBreak`'s value is `raft_init`'s. Re-review N2: the premise is `compactFloor ≤ applied` (the published floor and the base at most `applied`): with a restored snapshot pending, `committed = s.index` is past `applied` and the first index is `s.index + 1`, so Go's scan meets `ErrCompacted` and panics. `hup` calls it only after `promotable` (no pending snapshot: the base is then at most `applied`, the invariant's) and has the floor from `coreIdle_floor`.
Verify-round (RR-raft-core N3, S-e): the premise also takes `us.snap = none`: with a snapshot pending,
`base ≤ applied < committed` and `lastIndex < committed` (unstable entries empty, `offset = s.index + 1`)
is admitted by `Wf`, and Go's scan then panics (`log.go:562`). `hup` has `us.snap = none` from
`promotable` (`raft.go:1949`: `!hasNextOrInProgressSnapshot()`, i.e. `unstable.snapshot == nil`,
`log.go:290`), and `compactFloor ≤ applied` from `coreIdle_floor` (both `floor ≤ applied` and, the
snapshot absent, `base ≤ applied`).
-/
module

public import SpecPlan.Spec.go_etcd_io.raft.v3.ApiCore

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Raft

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- (internal) Whether a committed conf entry is not applied. -/
def raft.hasUnappliedConfChanges.spec : Prop :=
  ∀ (r : Loc) (γ : Cluster) (id : w64) (o : CoreOpen) ,
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ raftOpen r γ id o ∗
      ⌜o.log.us.snap = none ∧ o.log.compactFloor ≤ o.log.applied⌝ }}
    (App (Val (r @!! go.GoType.PointerType go_etcd_io.raft.v3.raft.ty @!! go!"hasUnappliedConfChanges")) (Val #()))
  {{ (b : Bool), RET #b; raftOpen r γ id o ∗ ⌜b = true ↔ o.unappliedConf⌝ }}

end spec
end Raft
end EtcdGrove
end Perennial

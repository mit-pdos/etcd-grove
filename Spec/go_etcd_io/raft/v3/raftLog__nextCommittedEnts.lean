/-
## `(*raftLog).nextCommittedEnts(allowUnstable)` (internal)

**Users**: `readyWithoutAccept` (`rawnode.go:144`: `Ready.CommittedEntries`, with
`applyUnstableEntries()`). Snippet `raftlog/ready.go` (`ReqCommittedForApply`).

**Proof sketch**: paused, a snapshot pending, or nothing to apply: `nil`. Else `maxSize =
max - size > 0` (`Wf`: unpaused has room, so the `Panicf` is excluded), and `slice(applying + 1,
maxAppliable + 1)`: `hi ≤ committed + 1 ≤ lastIndex + 1` (no snapshot pending: `lastIndex =
end`, `Wf`); no `ErrCompacted`, since `applying + 1 > applied ≥` the published floor and `>
base` (premise), so its `Panicf` is excluded.

**Changes**: from `specs-ref/Spec/go_etcd_io/raft/v3/raftLog__nextCommittedEnts.lean`: over `LogState`; the premise
`base ≤ applying` (outside `appliedSnap`'s window, where `applied` is below a just-stored
snapshot) replaces the old predicate's `Hpapplied`.

**Margin**: the size limit is not stated (the storage contract does not state sizes).
-/
module

public import Spec.go_etcd_io.raft.v3.ApiLog

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

/-- (internal) The committed entries to apply next: a non-empty prefix of `[applying+1, maxAppliable]`, or none when paused, a snapshot is pending, or nothing is committed past `applying`. -/
def raftLog.nextCommittedEnts.spec : Prop :=
  ∀ (l : Loc) (ls : LogState) (allow : Bool) (lo hi : Nat),
  (ls.us.snap = none → ls.base ≤ ls.applying) →
  lo = ls.applying + 1 → hi = ls.maxAppliable allow + 1 →
  (hi - lo < 2 ^ 63 ∨ ls.applyingPaused = true ∨ ls.us.snap.isSome) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ raftLog l ls }}
    (App (Val (l @!! go.GoType.PointerType go_etcd_io.raft.v3.raftLog.ty @!! go!"nextCommittedEnts")) (Val #allow))
  {{ (sl : GoSlice), RET #sl; raftLog l ls ∗ ∃ es, entriesRO sl lo es ∗
      ⌜es <+: ls.range lo hi ∧
       (es = [] ↔ (ls.applyingPaused = true ∨ ls.us.snap.isSome ∨ hi ≤ lo))⌝ }}

end spec
end Raft
end EtcdGrove
end Perennial

/-
## `ProgressTracker.Visit(f)`

**Users.** raft: `bcastAppend`, `bcastHeartbeat` (`raft.go:715`, `729`: send to each peer; the
callback reads `r.trk.Progress[id]` and writes the `Progress`), `reset` (`raft.go:813`: overwrites
each `Progress`, a fresh `Inflights`), `stepLeader`'s CheckQuorum (`raft.go:1306`: clears
`RecentActive`), `switchToConfig` (`raft.go:2023`: probe the peers), `getProgressCopy`
(`status.go:46`), `RawNode.WithProgress` (`rawnode.go:517`); `QuorumActive`. Snippet
`raftconf/tracker.go` (`ReqVisitSorted`).

**Proof sketch.** `n := len(p.Progress)`; the ids into a stack array or `make` (`range`, read
only), `slices.Sort` (`≤ 2^62`); for each `k`, `f(ids[k], p.Progress[ids[k]])`: a lookup (the
field and the map at `dq`) and the callback's triple from `I (take k)` to `I (take (k+1))`. Only the
`Progress` field and the map (not the `Progress` structs, not the configuration) are `Visit`'s: the
callback's own resources (`I`) hold whatever it touches, including another share of the map.

**Changes** (from `specs-ref`'s `tracker/ProgressTracker__Visit.lean`): the footprint is the
`Progress` field and the map at any share (was the whole tracker, which kept callbacks from reading
`r.trk`); the callback's invariant indexed by the sorted prefix visited (was the visited set and the
progress values).

**Margin.** None.
-/
module

public import Spec.go_etcd_io.raft.v3.tracker.Api

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Tracker

open Iris Iris.BI
open Classical

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.tracker.Assumptions]

/-- Calls `f(id, pr)` for each tracked peer, in increasing id order. -/
def ProgressTracker.Visit.spec : Prop :=
  ∀ (p : Loc) (mp : GoMap) (dq : DFrac) (prs : GMap w64 Loc) (f : GoFunc)
    (I : List w64 → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.tracker ∗
      typedPointsto (structFieldRef go_etcd_io.raft.v3.tracker.ProgressTracker go!"Progress" p)
        mp dq ∗ ownMap mp dq prs ∗ ⌜GMap.size prs ≤ Quorum.sortMax⌝ ∗
      I [] ∗
      (□ ∀ (k : Nat) (id : w64) (pr : Loc) (Φ : val → IProp GF),
        ⌜(Quorum.sorted (domSet prs))[k]? = some id ∧ prs !! id = some pr⌝ -∗
        I ((Quorum.sorted (domSet prs)).take k) -∗
        ▷ (I ((Quorum.sorted (domSet prs)).take (k + 1)) -∗ Φ #()) -∗
        WP (App (App (Val #f) (Val #id)) (Val #pr)) {{ Φ }}) }}
    (App (Val (p @!! go.GoType.PointerType go_etcd_io.raft.v3.tracker.ProgressTracker.ty @!! go!"Visit")) (Val #f))
  {{ RET #();
      typedPointsto (structFieldRef go_etcd_io.raft.v3.tracker.ProgressTracker go!"Progress" p)
        mp dq ∗ ownMap mp dq prs ∗ I (Quorum.sorted (domSet prs)) }}

end spec
end Tracker
end EtcdGrove
end Perennial

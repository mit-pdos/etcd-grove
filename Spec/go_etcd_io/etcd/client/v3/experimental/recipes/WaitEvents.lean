/-
`recipe.WaitEvents(c, key, rev, evs)` (`watch.go`): watch `key` from revision `rev` with a context of
its own (canceled on return) and `waitEvents`.

**Users**: `Barrier.Wait` (a delete), `DoubleBarrier.Enter` (the `ready` put), `Leave` (a delete),
`RWMutex.waitOnLastRev` (a delete). Exported; no caller outside the package. Snippet:
`recipes/watch.go`.

**Proof sketch**: `context.WithCancel(context.Background())` (W0's `Context.WithCancel.spec`:
`ctxOk`, `ctxChild` of `Background()`, so `ctxPrin` by `ctxPrin_background`, `ctxPrin_child`; and
the `cancel` function's `cancelOk`); `isClient_fields` (W0) gives the `Watcher` field with `watcherAt`; 1b's
`Watcher.Watch` triple at it with `OpWatch(key, WithRev(rev))` (W0's `OpWatch.spec`, `WithRev.spec`:
no range option) gives `watchChanAt wc γ {key, ""} rev []` (non-`nil`: the `ErrNoWatcher` branch is
dead, and allowed anyway); `waitEvents.spec`; the deferred `cancel()` (Perennial).

**Changes**: old spec required the recipes' client invariant, the key under its prefix and a size
bound, and stated the result through `waitedEvent`; now any client and key, the history fact.

**Premise**: `0 < rev`: a watch from revision `0` or below starts at the member's current revision,
which the spec would have to name; every caller passes a revision it read (`≥ 1`).

**Margin**: as `waitEvents`'.
-/
module

public import Spec.go_etcd_io.etcd.client.v3.experimental.recipes.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Recipes

open Iris Iris.BI EtcdModel EtcdWire ClientV3
open go_etcd_io.etcd.client.v3.experimental.recipes

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.experimental.recipes.Assumptions]

/-- **`WaitEvents(c, key, rev, ts)`**: the event at which `ts` is first matched by `key`'s events from revision `rev` on, or an error. -/
def WaitEvents.spec : Prop :=
  ∀ (c : Loc) (γ : Cluster) (who : Principal) (key : GoString) (rev : w64) (sl : GoSlice)
    (ts : List w32),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.experimental.recipes ∗ isClient c γ who ∗ sl ↦*□ ts ∗ ⌜ts ≠ [] ∧ 0 < sint.Z rev⌝ }}
    (App (App (App (App (Val (@! go_etcd_io.etcd.client.v3.experimental.recipes.WaitEvents)) (Val #c))
      (Val #key)) (Val #rev)) (Val #sl))

  {{ (ev : Loc) (err : GoInterface), RET (PairV #ev #err);
      (⌜err = GoInterface.nil⌝ ∗ ∃ (es : List WatchEv) (e : WatchEv) (σ : State),
        watchEvOwn ev e ∗ etcdLb γ σ ∗
        ⌜es ++ [e] <+: watchHist σ.kv { key := key, rangeEnd := [] } (sint.Z rev).toNat ∧ matchCount ts es < ts.length ∧
          matchCount ts (es ++ [e]) = ts.length⌝) ∨
      ⌜err ≠ GoInterface.nil ∧ ev = null⌝ }}

end spec

end Recipes
end EtcdGrove
end Perennial

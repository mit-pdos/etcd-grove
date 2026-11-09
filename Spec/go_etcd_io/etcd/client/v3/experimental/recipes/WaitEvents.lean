/-
`recipe.WaitEvents(c, key, rev, evs)` (`watch.go`): watch `key` from revision `rev` with a context of
its own (canceled on return) and `waitEvents`.

**Users**: `Barrier.Wait` (a delete), `DoubleBarrier.Enter` (the `ready` put), `Leave` (a delete),
`RWMutex.waitOnLastRev` (a delete). Exported; no caller outside the package. Snippet:
`recipes/watch.go`.

**Proof sketch**: `context.WithCancel(context.Background())` (W0's `Context.WithCancel.spec`:
`ctxOk`, `ctxChild` of `Background()`, so `ctxPrin` by `ctxPrin_background`, `ctxPrin_child`; and
the `cancel` function's `cancelOk`); `isClient_fields` (W0) gives the `Watcher` field with
`watcherAt`; 1b's `watcherAt_methods` gives `Watcher.WatchTriple` at it, with `OpWatch(key,
WithRev(rev))` (no range option: `watchPanics` false): `watchChAt wc γ who w (WatchPos.init rev r0)`
(or `WatchPos.closed rev`), `w` the request's `watchReq`, `done = some (rev - 1)` either way
(non-`nil`: the `ErrNoWatcher` branch is dead); `waitEvents.spec`;
the deferred `cancel()`.

**Changes**: old spec required the recipes' client invariant, the key under its prefix and a size
bound; now any client and key, the history fact over 1b's `watchEvents` of the watch as the member
reads it (an empty key is `"\x00"`: review 1f-provability-1, F1).

**Premise**: `0 < rev`: a watch from revision `0` or below starts at the member's current revision,
which the spec would have to name; every caller passes a revision it read (`≥ 1`).

**Margin**: as `waitEvents`'.

**Integration (I1)**: the prefix claim holds under `exactFrom σ.kv rev`, as `waitEvents`'.
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

/-- **`WaitEvents(c, key, rev, ts)`**: the event at which `ts` is first matched by the watch of `key` from revision `rev` on, or an error of the package. -/
def WaitEvents.spec : Prop :=
  ∀ (c : Loc) (γ : Cluster) (who : Principal) (key : GoString) (rev : w64) (sl : GoSlice)
    (ts : List w32),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.experimental.recipes ∗ isClient c γ who ∗ sl ↦*□ ts ∗ ⌜ts ≠ [] ∧ 0 < sint.Z rev⌝ }}
    (App (App (App (App (Val (@! go_etcd_io.etcd.client.v3.experimental.recipes.WaitEvents)) (Val #c))
      (Val #key)) (Val #rev)) (Val #sl))

  {{ (ev : Loc) (err : GoInterface), RET (PairV #ev #err);
      (⌜err = GoInterface.nil⌝ ∗ ∃ (es : List WEv) (e : WEv) (m : EventM) (σ : State),
        eventOwn ev (DFrac.own 1) m ∗ etcdLb γ σ ∗
        ⌜m.del = e.del ∧ m.kv = e.kv ∧
          (EtcdModel.exactFrom σ.kv (sint.Z rev).toNat →
            es ++ [e] <+: watchEvents (opWatchM key [withRevM rev]).watchReq σ.kv (sint.Z rev).toNat σ.kv.rev) ∧
          matchCount ts es < ts.length ∧ matchCount ts (es ++ [e]) = ts.length⌝) ∨
      (⌜err ≠ GoInterface.nil ∧ ev = null⌝ ∗ recipeErrOk err) }}

end spec

end Recipes
end EtcdGrove
end Perennial

/-
`recipe.WaitPrefixEvents(c, prefix, rev, evs)` (`watch.go`): `WaitEvents` over the keys with the
prefix (`WithPrefix()`).

**Users**: `Queue.Dequeue`, `PriorityQueue.Dequeue` (the first put). `T/v3_closed_watch_test.go:117`
(a compacted start revision: an error). Snippet: `recipes/queue.go`.

**Proof sketch**: as `WaitEvents`', with `OpWatch(prefix, WithPrefix(), WithRev(rev))` (its range is
`pfxRange prefix`).

**Changes**: as `WaitEvents`'.

**Premise**: as `WaitEvents`'.

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

/-- **`WaitPrefixEvents(c, prefix, rev, ts)`**: the event at which `ts` is first matched by the watch of the keys under `prefix` from revision `rev` on, or an error of the package. -/
def WaitPrefixEvents.spec : Prop :=
  ∀ (c : Loc) (γ : Cluster) (who : Principal) (pre : GoString) (rev : w64) (sl : GoSlice)
    (ts : List w32),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.experimental.recipes ∗ isClient c γ who ∗ sl ↦*□ ts ∗ ⌜ts ≠ [] ∧ 0 < sint.Z rev⌝ }}
    (App (App (App (App (Val (@! go_etcd_io.etcd.client.v3.experimental.recipes.WaitPrefixEvents)) (Val #c))
      (Val #pre)) (Val #rev)) (Val #sl))

  {{ (ev : Loc) (err : GoInterface), RET (PairV #ev #err);
      (⌜err = GoInterface.nil⌝ ∗ ∃ (es : List WEv) (e : WEv) (m : EventM) (σ : State),
        eventOwn ev (DFrac.own 1) m ∗ etcdLb γ σ ∗
        ⌜m.del = e.del ∧ m.kv = e.kv ∧ es ++ [e] <+: watchEvents (opWatchM pre [withPrefixM, withRevM rev]).watchReq σ.kv (sint.Z rev).toNat σ.kv.rev ∧
          matchCount ts es < ts.length ∧ matchCount ts (es ++ [e]) = ts.length⌝) ∨
      (⌜err ≠ GoInterface.nil ∧ ev = null⌝ ∗ recipeErrOk err) }}

end spec

end Recipes
end EtcdGrove
end Perennial

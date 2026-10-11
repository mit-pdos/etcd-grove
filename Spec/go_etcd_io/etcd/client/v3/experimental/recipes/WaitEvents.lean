/-
`recipes.WaitEvents(c, key, rev, evs)` (`client/v3/experimental/recipes/watch.go`). Lean-first (no Rocq counterpart);
see `InvRecipesClient.lean`.
-/
module

public import Proof.go_etcd_io.etcd.client.v3.experimental.recipes.InvRecipesClient

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace recipes

open Iris Iris.BI go_etcd_io.etcd.client.v3.experimental.recipes go_etcd_io.etcd.api.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.experimental.recipes.Assumptions]

/-- **`WaitEvents(c, key, rev, evs)`**, for a client with the recipes' contracts on the prefix `pfx`
(`isEtcdRecipesClient`: **its watch channels never close**, the premise) and a non-empty
read-only slice of event types whose last is `typ`: a cancelable context
(`WithCancel(Background())`, canceled on return by the deferred `cancel()`), the watch
`Watch(key, WithRev(rev))` through the client's `Watcher` (`c.Watcher.Watch`), and `waitEvents` on its channel.
Returns `(ev, nil)` with `ev` the event of type `typ` that completed the awaited types, under
etcd's contract for an event of that watch (`waitedEvent`: at a revision at least `rev` etcd
has reached; for a delete of the key, the key absent then: `waitedEvent_key_delete`; for a put,
the key-value then: `waitedEvent_put`). Never `ErrNoWatcher`: the watcher's channel is a channel,
not nil (`isChan_not_null`); never `(nil, nil)`: the premise. -/
abbrev WaitEvents.spec : Prop :=
  ∀ (c : Loc) (pfx key : GoString) (rev : w64) (sl : GoSlice) (ts : List w32) (typ : w32),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.experimental.recipes ∗ context.isClosedchanInit ∗ isEtcdRecipesClient c pfx ∗ sl ↦*□ ts ∗
      ⌜ts.getLast? = some typ ∧ pfx <+: key ∧ 0 ≤ sint.Z rev⌝ }}
    (App (App (App (App (Val (@! go_etcd_io.etcd.client.v3.experimental.recipes.WaitEvents)) (Val #c))
      (Val #key)) (Val #rev)) (Val #sl))
  {{ (ev : Loc) (err : GoInterface), RET (PairV #ev #err);
      ⌜err = GoInterface.nil⌝ ∗ waitedEvent pfx (keyWatchOp key rev) rev typ ev }}

end spec

end recipes
end EtcdGrove
end Perennial

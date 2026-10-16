/-
`recipes.waitEvents(wc, evs)` (`client/v3/experimental/recipes/watch.go`). Lean-first (no Rocq counterpart);
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
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [EM : EtcdModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.experimental.recipes.Assumptions]

/-- **`waitEvents(wc, evs)`**, for the channel `wc` of a range watch `o` (under `pfx`) from
`rev`, which may be closed at any time (the SPSC channel's close predicate is `True`: the
bundle's `isEtcdRangeWatcher`), consumed by the caller, and a non-empty read-only slice of event
types whose last is `typ`: receives responses until it has seen the types in order. Returns
* `(ev, nil)` with `ev` the event that completes them, of type `typ`, with etcd's contract for it
  (`waitedEvent`), and the consumer token back;
* `(nil, err)` with `err ≠ nil` when a response is canceled or carries an error
  (`wresp.Err()`, before its events are read) or the channel closes first (`ErrWatchClosed`,
  the verified fork's fix, unit W-Q); the consumer token is not returned (a close puts it
  in the channel's invariant, `spsc_rcv_au`). -/
abbrev waitEvents.spec : Prop :=
  ∀ (wc : Loc) (γ : EtcdWatchNames) (pfx : GoString) (o : OpFull) (rev : w64)
    (rcv : List go_etcd_io.etcd.client.v3.WatchResponse) (sl : GoSlice) (ts : List w32)
    (typ : w32),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.experimental.recipes ∗
      isSpsc (GF := GF) γ.spsc wc (rangeWatchElem γ pfx o rev) (fun _ => iprop(True)) ∗
      spscConsumer γ.spsc rcv ∗ sl ↦*□ ts ∗ ⌜ts.getLast? = some typ⌝ }}
    (App (App (Val (@! go_etcd_io.etcd.client.v3.experimental.recipes.waitEvents)) (Val #wc))
      (Val #sl))
  {{ (ev : Loc) (err : GoInterface), RET (PairV #ev #err);
      (⌜err = GoInterface.nil⌝ ∗ waitedEvent pfx o rev typ ev ∗
        ∃ rcv' : List go_etcd_io.etcd.client.v3.WatchResponse, spscConsumer γ.spsc rcv') ∨
      ⌜err ≠ GoInterface.nil ∧ ev = null⌝ }}

end spec

end recipes
end EtcdGrove
end Perennial

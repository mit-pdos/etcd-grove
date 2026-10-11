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
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.experimental.recipes.Assumptions]

/-- **`waitEvents(wc, evs)`**, for the channel `wc` of a range watch `o` (under `pfx`) from
`rev`, **never closed** (the SPSC channel's close predicate is `False`: the premise of the
bundle's `isEtcdRangeWatcherOpen`), consumed by the caller, and a non-empty read-only slice of
event types whose last is `typ`: receives responses until it has seen the types in order, and
returns the event that completes them, of type `typ`, with etcd's contract for it
(`waitedEvent`). It never returns `nil`: that happens only when the channel closes, which the
premise excludes (on a close the code as shipped returns `nil`, the recipes' findings). -/
abbrev waitEvents.spec : Prop :=
  ∀ (wc : Loc) (γ : EtcdWatchNames) (pfx : GoString) (o : OpFull) (rev : w64)
    (rcv : List go_etcd_io.etcd.client.v3.WatchResponse) (sl : GoSlice) (ts : List w32)
    (typ : w32),
  {{ isSpsc γ.spsc wc (rangeWatchElem γ pfx o rev) (fun _ => iprop(False)) ∗
      spscConsumer γ.spsc rcv ∗ sl ↦*□ ts ∗ ⌜ts.getLast? = some typ⌝ }}
    (App (App (Val (@! go_etcd_io.etcd.client.v3.experimental.recipes.waitEvents)) (Val #wc))
      (Val #sl))
  {{ (ev : Loc), RET #ev; waitedEvent pfx o rev typ ev ∗
      ∃ rcv' : List go_etcd_io.etcd.client.v3.WatchResponse, spscConsumer γ.spsc rcv' }}

end spec

end recipes
end EtcdGrove
end Perennial

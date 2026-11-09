/-
`recipe.waitEvents(wc, evs)` (`watch.go`): receive from the watch channel until the events' types have
matched `evs` in order (greedily), and return the last matching event; an error response's error, or
`ErrWatchClosed` if the channel closes first.

**Users**: `WaitEvents`, `WaitPrefixEvents`. Internal.

**Proof sketch**: a loop over receives (`chan.forRange`) carrying 1b's `watchChAt wc γ who w p`, the
events `es` received so far and `i = matchCount ts es`, with: `p.done = some c` and, under `exactFrom σ.kv rev`,
`es` exactly `watchEvents w σ.kv rev c` for the latest response's `etcdLb γ σ` (`etcdLb_ord`: the
history only grows, so earlier responses' events stay `σ`'s, and the condition at `σ` implies it at
the earlier responses' states, whose `watchStep` gives their events under it from `lo = c + 1 ≥ rev`). `watchChAt_recv` (1b) gives the channel closed
(return `ErrWatchClosed`: `init.spec`) or a response `m` with `watchStep`: `WatchResponse.Err.spec`
(1b) on the response's copy, with `watchRespAt_fields`' `closeErrOk`, returns `callErr err ck`,
`errVal .compacted`/`.futureRev`, or a `callErr` (all `recipeErrOk`) for an error response, `nil`
otherwise; a response with events extends `es` by `watchEvents w σ.kv (c + 1) c'` (`watchStep`'s
events case, from `p.done = some c`, which starts at `rev - 1`: `Watch`'s `WatchPos.init rev r0` or
`WatchPos.closed rev`, whichever it returned); the inner loop
reads each event's `Type` (`eventOwn_unfold`: `1` iff `del`) and compares it with `ts[i]` (`i <
ts.length` throughout: in bounds); when `i` reaches `ts.length` it returns that event's pointer,
with its `eventOwn` (the response's events are owned in full) and `m.kv = e.kv` (`EventM.isOf`). A
progress notification or a `Created` response adds nothing.

**Changes**: old spec was over Perennial's SPSC channel of the old watch and required the channel
never to close (the fixed bug); round 1 used a slot of its own; now 1b's `watchChAt` and
`WatchResponse.Err.spec` (review 1f-provability-1, S1), the errors `recipeErrOk` (F3).

**Premise**: `ts ≠ []` (with no type to match, the first event indexes `evs[0]` and panics); a watch
from a revision `rev > 0`.

**Changes (second pass)**: the returned event is, unconditionally, a real event of some revision that the watch keeps (in its range, of its types): 1b's `watchStep` now states this outside the `exactFrom` gate; the prefix of the history stays gated.

**Margin**: the events of the responses after the match are not reported (the code drops them).

**Integration (I1)**: the prefix claim (`es ++ [e]` a prefix of `watchEvents`) is gated by the compaction condition `exactFrom σ.kv rev` (W0's
`EtcdModel.exactFrom`): 1b's `watchStep` gives a response's events (and a progress's emptiness) only
under it, so the facts this call learns from a watch hold only under it; the condition at the last
response's state implies it at every earlier one (the history only grows, compaction only rises). The weakest condition the watches need: they start at or after that revision.
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

/-- **`waitEvents(wc, ts)`**: the event at which the types `ts` are first matched, in order, by the watch's events (a prefix of its events in the history from `rev`), or an error of the package. -/
def waitEvents.spec : Prop :=
  ∀ (wc : Loc) (γ : Cluster) (who : Principal) (w : WatchReq) (p : WatchPos) (rev : Nat)
    (sl : GoSlice) (ts : List w32),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.experimental.recipes ∗ watchChAt wc γ who w p ∗ sl ↦*□ ts ∗ ⌜ts ≠ [] ∧ 0 < rev ∧ p.done = some (rev - 1)⌝ }}
    (App (App (Val (@! go_etcd_io.etcd.client.v3.experimental.recipes.waitEvents)) (Val #wc)) (Val #sl))

  {{ (ev : Loc) (err : GoInterface), RET (PairV #ev #err);
      (⌜err = GoInterface.nil⌝ ∗ ∃ (es : List WEv) (e : WEv) (m : EventM) (σ : State),
        eventOwn ev (DFrac.own 1) m ∗ etcdLb γ σ ∗
        ⌜m.del = e.del ∧ m.kv = e.kv ∧
          (∃ (r : Nat) (ev0 : Event), ev0 ∈ σ.kv.eventsAt r ∧ (WEv.ofEvent r ev0).del = e.del ∧
            (WEv.ofEvent r ev0).kv = e.kv ∧ w.keeps (WEv.ofEvent r ev0)) ∧
          (EtcdModel.exactFrom σ.kv rev → es ++ [e] <+: watchEvents w σ.kv rev σ.kv.rev) ∧
          matchCount ts es < ts.length ∧ matchCount ts (es ++ [e]) = ts.length⌝) ∨
      (⌜err ≠ GoInterface.nil ∧ ev = null⌝ ∗ recipeErrOk err) }}

end spec

end Recipes
end EtcdGrove
end Perennial

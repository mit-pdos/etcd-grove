/-
`recipe.waitEvents(wc, evs)` (`watch.go`): receive from the watch channel until the events' types have
matched `evs` in order (greedily), and return the last matching event; an error response's error, or
`ErrWatchClosed` if the channel closes first.

**Users**: `WaitEvents`, `WaitPrefixEvents`. Internal.

**Proof sketch**: a loop over receives (`chan.forRange`) carrying `watchChanAt wc γ rg rev (seen ++
es)` and `i = matchCount ts es`: `watchChanAt_recv` (1b's slot) gives a closed channel (return
`ErrWatchClosed`, `init.spec`, `recipeErr_ne`), an error response (`WatchResponse.Err` (1b) returns
non-`nil` when `closeErr`, `CompactRevision` or `Canceled` is set), or events extending the history
prefix (`Err()` returns `nil`; the inner loop reads each event's `Type` through `watchEvOwn_unfold`
and compares it with `ts[i]`: `i < ts.length` throughout, so the index is in bounds; when `i` reaches
`ts.length` it returns that event with the `etcdLb` of the response that carried it).

**Changes**: old spec was over Perennial's SPSC channel of the old watch (`isSpsc`,
`rangeWatchElem`) and required the channel never to close (the fixed bug); now over 1b's
`watchChanAt`, which may close.

**Premise**: `ts ≠ []`: with no type to match, the first event indexes `evs[0]` and panics.

**Margin**: the events of the responses after the match are not reported (the code drops them).
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

/-- **`waitEvents(wc, ts)`**: the event at which the types `ts` are first matched, in order, by the watch's events (a prefix of the range's history from `rev`), or an error. -/
def waitEvents.spec : Prop :=
  ∀ (wc : Loc) (γ : Cluster) (rg : KeyRange) (rev : Nat) (seen : List WatchEv) (sl : GoSlice)
    (ts : List w32),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.experimental.recipes ∗ watchChanAt wc γ rg rev seen ∗ sl ↦*□ ts ∗ ⌜ts ≠ []⌝ }}
    (App (App (Val (@! go_etcd_io.etcd.client.v3.experimental.recipes.waitEvents)) (Val #wc)) (Val #sl))

  {{ (ev : Loc) (err : GoInterface), RET (PairV #ev #err);
      (⌜err = GoInterface.nil⌝ ∗ ∃ (es : List WatchEv) (e : WatchEv) (σ : State),
        watchEvOwn ev e ∗ etcdLb γ σ ∗
        ⌜seen ++ es ++ [e] <+: watchHist σ.kv rg rev ∧ matchCount ts es < ts.length ∧
          matchCount ts (es ++ [e]) = ts.length⌝) ∨
      ⌜err ≠ GoInterface.nil ∧ ev = null⌝ }}

end spec

end Recipes
end EtcdGrove
end Perennial

# Goose: array indexing emits `IndexRef` applied to a *loaded array value*

**Component:** Goose (the Go → Rocq translator), array indexing
**Status:** open, 2026-09-16
**Found while:** proving `wp_campaign_peer_ids`, the peer enumeration
`campaign` uses to address its `MsgVote`s.

## What breaks

Every array index in the translated raft code is **stuck** — the model has no
rule that matches the expression Goose emits, so no proof can step past it.

`quorum.JointConfig` is an array (`new/code/go_etcd_io/raft/v3/quorum.v:552`):

```coq
Definition JointConfigⁱᵐᵖˡ : go.type := go.ArrayType 2 MajorityConfig.
```

`JointConfig.IDs` reads `c[0]`, and Goose translates it as
(`new/code/go_etcd_io/raft/v3/quorum.v:82`, and `:94` for `c[1]`):

```coq
let: "$range" := ![MajorityConfig] (IndexRef JointConfig (![JointConfig] "c", #(W64 0))) in
```

Note the operand: `![JointConfig] "c"`. Goose **loads the whole array out of
the frame slot** and then asks `IndexRef` for a reference *into the loaded
value*. There is no address in a loaded value to take a reference into.

The frame slot `"c"` is itself the address — `IDs` opens with
`let: "c" := GoAlloc JointConfig "c"` — so the operand should be `"c"`, not
`![JointConfig] "c"`.

## Why it is stuck, not merely awkward

The two index rules in `new/golang/defn/array.v` are asymmetric in exactly the
way that matters:

| rule | line | operand |
|---|---|---|
| `index_ref_array` | `new/golang/defn/array.v:50` | `(#l, #i)` with **`l : loc`** |
| `index_array` | `new/golang/defn/array.v:54` | `(#a, #i)` with **`a : array.t V n`** |

`array.t` is `Inductive t (V : Type) (n : Z) := mk (arr : list V)`
(`src/goose_lang/lang.v:529`) — a list, carrying **no address at all**. So
`IndexRef` on an array value cannot be given a rule; the information is not
there.

Contrast slices, where Goose's "load the operand" shape is correct:
`index_ref_slice` (`new/golang/defn/slice.v:122`) does take a slice *value*,
because a `slice.t` value carries `slice.ptr`. It looks like the array case
inherited the slice case's treatment.

Probes (each `rocq compile -vok`, clean):

| goal | result |
|---|---|
| `WP IndexRef quorum.JointConfig (#(l : loc), #(W64 0))` | steps → `Φ #(array_index_ref map.t 0 l)` |
| `WP IndexRef quorum.JointConfig (#(a : array.t loc 2), #(W64 0))` | **stuck** — `wp_auto`: `Failed to progress` |
| `WP Index quorum.JointConfig (#(a : array.t loc 2), #(W64 0))` | steps → `match array.arr a !! 0 with …` |

## Scope

Every array index in the translated etcd-raft code, which is 19 sites:

- 16 in `quorum.JointConfig` — `IDs` (2), `String` (3), `CommittedIndex` (2),
  `VoteResult` (2), plus the `quorum.`-qualified occurrences in
  `new/code/go_etcd_io/raft/v3.v` and
  `new/code/go_etcd_io/raft/v3/tracker.v`.
- 3 indexes of a package-level array through `GlobalVarAddr`, which take the
  same wrong shape (`![go.ArrayType n T] (GlobalVarAddr … #())`):
  `prstmap` (`tracker.v:560`), `_VoteResult_index` (`quorum.v:492`),
  `stmap` (`v3.v:2788`).

No slice index is affected (80 sites, all fine).

## Fix

In Goose, do not deref the operand of an array index: emit
`IndexRef T ("c", i)` when the array is addressable. For the two occurrences
in `IDs` the value form `Index T (![T] "c", i)` would also work, since they
are plain reads — but `String`, `CommittedIndex` and `VoteResult` use the
result as a **pointer receiver**
(`MethodResolve (go.PointerType MajorityConfig) …`), so those genuinely need
the address and only the `IndexRef T ("c", i)` fix covers them.

Goose is not checked out in this repo; see
[../notes/goose-workflow.md](../notes/goose-workflow.md) for the
regeneration path.

## Blocked until it lands

- **`wp_campaign_peer_ids`** (`new/proof/go_etcd_io/raft/v3_proof/election/inv_misc.v`)
  — was an `Axiom`, now an `Admitted` `Lemma` with the machine-checked prefix
  banked up to the stuck `IndexRef`. Past that point nothing is missing: the
  rest is a `wp_map_for_range` over `voters_ref` (`own_tracker`'s
  `Hvoters_dom` gives `dom voters = cfg`) plus `wp_map_nil_for_range`
  (`new/golang/theory/map.v:305`) for the nil second component. `slices.Sort`
  is *not* involved — that sort is in `campaign`, not in `IDs`.
- **`wp_JointConfig__CommittedIndex`**
  (`new/proof/go_etcd_io/raft/v3_proof/readonly.v:718`) — an `Axiom` for this
  same reason.
- `JointConfig`'s `VoteResult`, `String` and `Describe`, if they are ever
  needed.

## Related

`into_val_typed_array` (`new/golang/theory/array.v:57`) is itself `Admitted`
with an `admit` inside, so array support in this `new/golang` is visibly
work in progress. A fix on the Goose side should be paired with a look at
whether the array theory is complete enough to use.

# Goose: array operations are emitted against a *loaded array value*

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

## The same defect for `Slice`, and a missing rule for `len`

`ProgressTracker.Visit` has `var sl [7]uint64; … ids = sl[:n]`, and
`new/code/go_etcd_io/raft/v3/tracker.v:816-817` emits

```coq
let: "$s" := ![go.ArrayType 7 go.uint64] "sl" in
Slice (go.ArrayType 7 go.uint64) ("$s", #(W64 0), ![go.int] "n")
```

— again the loaded value, while `slice_array_step`
(`new/golang/defn/array.v:80`) steps only on `(#p, #low, #high)` with
`p : loc`. It is also *semantically* wrong independently of the model: in Go
`sl[:n]` aliases `sl`, and a slice of a copy does not.

Two lines above it, `len(sl)` on an array (`tracker.v:815`):

```coq
(FuncResolve go.len [go.ArrayType 7 go.uint64] #()) ≥⟨go.int⟩ ![go.int] "n"
```

This one is a **gap in `new/golang`, not a Goose bug**: there is no
`FuncUnfold go.len [go.ArrayType n t]` instance anywhere under
`new/golang/` (`grep -rn "go.len" new/golang/defn/array.v
new/golang/theory/array.v` finds nothing), and `go.len_underlying` cannot
help because an array type is its own underlying type. `wp_auto` parks on a
bare `#(functions go.len [go.ArrayType 7 go.uint64])`.

Related and cheaper to fix: `new/golang/defn/map.v` declares its `FuncUnfold`s
at the literal `go.MapType`, so `len` of a *named* map type needs
`go.len_underlying` + `go.is_underlying` by hand — unlike `slice.v:133`,
which takes any `st ↓u go.SliceType elem_type`. `wp_ProgressMap_len` in
`election/inv_tracker.v` is that workaround.

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

Two parts.

**In Goose:** do not deref the operand of an array operation. Emit
`IndexRef T ("c", i)` and `Slice T ("sl", lo, hi)` when the array is
addressable. For the two index occurrences in `IDs` the value form
`Index T (![T] "c", i)` would also work, since they are plain reads — but
`String`, `CommittedIndex` and `VoteResult` use the result as a **pointer
receiver** (`MethodResolve (go.PointerType MajorityConfig) …`), so those
genuinely need the address and only the `IndexRef T ("c", i)` fix covers
them. `Slice` has no value form at all, and needs the address anyway to get
Go's aliasing right.

Goose is not checked out in this repo; see
[../notes/goose-workflow.md](../notes/goose-workflow.md) for the
regeneration path.

**In `new/golang/defn/array.v`:** add a `FuncUnfold go.len [go.ArrayType n t]`
instance returning `#(W64 n)`. Independent of the Goose fix, and needed as
well as it.

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
- **`wp_ProgressTracker__TallyVotes`**
  (`new/proof/go_etcd_io/raft/v3_proof/election/inv_tracker.v`) — the whole
  tally loop is proved and banked; it parks on the function's last statement,
  `p.Config.Voters.VoteResult(p.Votes)`, at `quorum.v:154`. Two further
  obstacles sit behind the array fix, both recorded in that file: the joint
  config's second component is `map.nil` and `MajorityConfig.VoteResult`
  opens with `len(c) == 0`, which unfolds to a read of the null location with
  no nil-map instance for `go.len` (the ranging case has
  `wp_map_nil_for_range`; `len` has no counterpart) — *not yet probed*; and
  the lemma's `VoteWon` conjunct is false at `cfg = ∅`, which is a statement
  bug rather than a tooling one (see notes/STATUS.md).
- **`wp_ProgressTracker__Visit`** (same file) — blocked on *both* the `Slice`
  defect and the missing array `len`, on the `len(sl) >= n` fast path. The
  `else` branch (`make([]uint64, n)`, taken when `size cfg > 7`) is fine;
  only the fast path is stuck. Its statement was separately found false and
  has been repaired — again see notes/STATUS.md.
- `JointConfig`'s `String` and `Describe`, if they are ever needed.

## Related

`into_val_typed_array` (`new/golang/theory/array.v:57`) is itself `Admitted`
with an `admit` inside, so array support in this `new/golang` is visibly
work in progress. A fix on the Goose side should be paired with a look at
whether the array theory is complete enough to use.

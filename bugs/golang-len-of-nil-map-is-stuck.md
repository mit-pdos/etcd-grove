# `new/golang`: `len` of a nil map has no rule

**Component:** the `new/golang` model, `go.len` on maps
**Status:** open, measured 2026-09-17
**Split out of:** `goose-array-indexref-loads-its-operand.md` (fixed and
deleted on 2026-09-17), which flagged this as a second obstacle on
`wp_ProgressTracker__TallyVotes` but recorded it as *not yet probed*. It has
now been probed; this file is the measurement.

## What breaks

In Go, `len(m)` for a nil map `m` is `0`, and is perfectly safe — nil maps
read as empty. The model has no rule that gets there.

`new/golang/defn/map.v:137` gives `len` on a map this body:

```coq
  #[global] len_map key_type elem_type ::
    FuncUnfold go.len [go.MapType key_type elem_type]
    (λ: "m", InternalMapLength (Read "m"))%V;
```

`Read "m"` at `m = map.nil` is a read of the null location, and
`InternalMapLength` (`map.v:67`) is stated only for a map value. There is no
nil-map case for `go.len`, unlike ranging, which has
`wp_map_nil_for_range` (`new/golang/theory/map.v:305`).

There is also no `PureWp` instance for `go.len` on a map at all — contrast
`pure_wp_slice_len` (`new/golang/theory/slice.v:335`) — so `wp_auto` cannot
even unfold it; stepping a map `len` needs `wp_map_len` and therefore
`own_map` ownership, which a nil map has none of.

## Evidence

Probe, `rocq compile -vok`, RC=0, against `new/golang/theory/` at the
2026-09-17 array fix:

```coq
Lemma probe_nil_map_len Φ :
  Φ #(W64 0) -∗
  WP (FuncResolve go.len [go.MapType go.uint64 go.bool] #() #map.nil) {{ Φ }}.
Proof. iIntros "HΦ". wp_auto. Show. Abort.
```

`wp_auto` leaves the goal **untouched**:

```
WP # (functions go.len [go.MapType go.uint64 go.bool]) (# map.nil) {{ v, Φ v }}
```

So this is stuck, not merely awkward — the same shape of finding as the array
`IndexRef` one, and for the same reason: no rule matches.

## Fix

Two plausible shapes, not yet chosen:

- a nil case on `go.len` for maps, mirroring `wp_map_nil_for_range` — i.e. a
  `PureWp True (#(functions go.len [st]) #map.nil) #(W64 0)`, which needs
  `InternalMapLength` (or the `len_map` body) to have a nil case in
  `new/golang/defn/map.v`. This is a **TCB** change, so it wants the same care
  the array `len` rule got: Go's `len(nil map) = 0` is unambiguous, but the
  guard style of the file should be matched.
- or: make `own_map` cover the nil map, so that a nil map is ownable and the
  ordinary `wp_map_len` applies.

Related and cheaper, also noted in the deleted file: `new/golang/defn/map.v`
declares its `FuncUnfold`s at the literal `go.MapType`, so `len` of a *named*
map type needs `go.len_underlying` + `go.is_underlying` by hand — unlike
`slice.v:133` and the array rules added on 2026-09-17, which take any
`st ↓u …`. `wp_ProgressMap_len` in
`new/proof/go_etcd_io/raft/v3_proof/election/inv_tracker.v` is that
workaround.

## Blocked until it lands

- **`wp_ProgressTracker__TallyVotes`**
  (`new/proof/go_etcd_io/raft/v3_proof/election/inv_tracker.v`). The array
  obstacle on this lemma is gone as of 2026-09-17, but the joint config's
  second component is `map.nil` (`own_tracker`'s `Hvoters_arr`) and
  `MajorityConfig.VoteResult` opens with `len(c) == 0`, so the second
  component's tally parks here.

  Note that this lemma *also* has a statement bug independent of any tooling:
  its `VoteWon` conjunct is false at `cfg = ∅`. See that file's comment and
  `notes/STATUS.md`.

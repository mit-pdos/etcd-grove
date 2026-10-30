# logkvcompact: the base proof adapted to log compaction (2026-10-28, branch `logkv-eval`)

One variant of the scalable-proof experiment (`notes/logkv-eval.md`): `examples/lintest/logkvcompact`
is `logkv` with log compaction. The log keeps only the writes not yet applied, numbered from an
offset `start`; the apply goroutine, once caught up, drops what it applied (`s.log =
s.log[s.applied-s.start:]; s.start = s.applied`), and `Put`'s index is `s.start + len(s.log)`.

**Result**: `logkvcompact_adequate` (`Proof/.../lintest/logkvcompact/Adequacy.lean`), the same
statement as `logkv_adequate`: every execution of `initialize'(); Main()` of fewer than `2^63`
steps never gets stuck and no thread panics. `#print axioms`: the same 53 entries as
`logkv_adequate` (compared as sets: equal; no `sorryAx`, no new axiom). `Adequacy.lean`,
`Results.lean`, `Link.lean`, `Init.lean` and `PkgTable.lean` are the base's, renamed, unchanged
(`etc/gen-link.py --lintest-logkvcompact` and `etc/gen-init.py <pkg>` regenerate them identically;
`etc/gen-init.py --check` passes on all 170 files, `PkgTable` included).

Method: the base's `Spec/` and `Proof/` copied with the package renamed (commit `e5ae49e803`,
"logkvcompact: copy of the base"), then changed only where the build failed.

## What changed, and why

### 1. The lock invariant: the log is a suffix of the requests (the feature)

`logkvcompactR` gains the offset `b` (`s.start`, its points-to `startAddr s ↦ b`), and the log
slice holds `(rs.drop b).map fst` instead of `rs.map fst`; `b ≤ applied`. Everything else of the
base's invariant carried over as it was: `rs` stays the list of *all* requests ever made (the
ghost history, in the same monotone list), the done/pending split at `applied` is unchanged, and
so are `pendSlot`, `doneSlot`, `regAu`, the helping protocol and the saved-proposition trick.
That `rs` was already a ghost list separate from the slice is what made this cheap: compaction
drops points-tos, never ghost state.

Proof cost: `applyLoop` reads entry `applied - start` (`Hidx`, `Hlook`: offset arithmetic), and
the caught-up branch is new code: `ownSlice_slice_with_cap` (Perennial) splits the slice at
`applied - start = len`, the dropped prefix's points-to is thrown away, the rest of the backing
array becomes the new slice's capacity; the invariant is re-established with `start = applied`
(the new log is empty: `subslice len len _ = []`). `Put`'s re-establishment after `append` adds
one `List.drop_append_of_le_length`.

Required by the feature. A base design that would have avoided it: none reasonable; the base's
log *is* the request list, and saying "the log is the suffix from 0" up front would have been
speculative generality.

### 2. A bound on the number of writes: time receipts (the feature, through `uint64` wrap-around)

In the base, the number of writes is `len(s.log)`, a slice length, which cannot wrap. With
compaction it is `s.start + uint64(len(s.log))`, a `uint64` sum, and the code is wrong if it
wraps: after `2^64` writes, `Put`'s `idx` wraps to a small value, `applied < idx` is false, and
`Put` returns before its write is applied (a linearizability violation, not a panic); the apply
loop's `applied < start + len` also stops. So the proof needs `|rs| < 2^64`, and nothing in the
base bounds the number of `Put` calls.

The fix is the one `CounterClock` uses: time receipts. `Put` takes a receipt at the resolution of
`Lock` (`wp_take_receipt`, `Proof/ReceiptTactics.lean`), the lock invariant keeps `⧗ |rs|` (one
per write) and `⌜|rs| < 2^64⌝`, and `receipt_add_one_lt` gives `|rs| + 1 < receiptBound GF`. The
bound `receiptBound GF ≤ 2^64` lives in `isServer` (a pure conjunct), so:

- **Specs changed**: `New.spec` takes `receiptBound GF ≤ 2 ^ 64 →` (it establishes `isServer`),
  and so does `Check.spec` (it calls `New`; a last premise). `Main.spec` is unchanged: it already
  had `receiptBound GF ≤ 2^63` (for the clock), and passes `≤ 2^64` on (one line). `Put`, `Get`,
  `Apply`, `Model`, `applyLoop` specs: unchanged.
- The adequacy theorem is unchanged (its `n < 2^63` already implied the bound).

Spec design (the `spec` skill): the premise is one the code needs (hard rule "no unneeded
premise": the code is wrong past `2^64` writes), its source is visible to every client (the
adequacy bound, as for `CounterClock`), and it is placed where it costs fewest specs: in
`isServer`, established once by `New`, rather than on `Put` (which would have changed `Put`,
`Apply` and `Check`). It does not mention the log. A per-server token budget of writes was the
alternative; it would have changed `Put`'s and `Apply`'s specs and the driver's contract, for no
gain.

Required by the feature (it is the feature's arithmetic, not the base's specs). Not filed in
`issues/`: `2^64` writes are not reachable in practice, and the same holds of any Go counter.

### 3. Bookkeeping forced by the base's proof style (not by the feature)

- **Positional destructuring of the lock invariant**: every `icases HR with ⟨%sl, %rs, %a, %st,
  Hlog, …⟩`, its `iexists sl, rs, a, st` and its frame lists (`[Hlog Hsl Hcap Happ …]`) grew by
  `b`, `Hstart`, `Hrc`: 4 places in `Put`, 2 in `Get`, 2 in `applyLoop`. `Get` changed (6 lines)
  although it reads only `s.state`: it destructures the whole invariant to reach the state's
  points-to and half of `γ`.
- **Positional destructuring of `isServer`**: the new pure conjunct changed the `icases Hs` line
  of `Put`, `Get` and `applyLoop`.

A base design that would have avoided these: the lock invariant as a separating conjunction of
named pieces (`stateRes γ s st ∗ logRes γ γr s`), with `Get` opening only `stateRes` and the log
proofs re-establishing `logRes` through a lemma, and `isServer` with its pure facts in a record or
behind laws; then `Get` would have been untouched and the other proofs would have changed only
in the log piece. In this small package these cost ~20 changed lines, about a fifth of the churn.

### What carried over unchanged

`Model` (spec and proof), `Server.Apply` (spec and proof), `Get`'s spec, `Put`'s spec,
`applyLoop`'s spec, the model `regS` and its lemmas, `regState`, `regAu`, `pendSlot`,
`doneSlot`, the whole helping argument (linearization point in `applyLoop`, the writer's
collection through the saved proposition and the ticket), `Check`'s generator proof, `Main`'s
proof (but one argument), `Adequacy`, `Results`, `Link`, `Init`, `PkgTable`.

## Changes outside my paths

None needed. (Perennial already had what compaction needs: `ownSlice_slice_with_cap` for
`s[k:]` keeping the capacity, the slice-slice step, receipts.)

## Numbers

`git diff --stat e5ae49e803..HEAD -- Spec/.../logkvcompact Proof/.../logkvcompact` (before this
notes file):

```
 Proof/.../logkvcompact/Check.lean              |  4 +-
 Proof/.../logkvcompact/Defs.lean               | 28 +++++---
 Proof/.../logkvcompact/Main.lean               |  3 +-
 Proof/.../logkvcompact/New.lean                |  9 ++-
 Proof/.../logkvcompact/Server__Get.lean        |  9 +--
 Proof/.../logkvcompact/Server__Put.lean        | 48 +++++++++-----
 Proof/.../logkvcompact/Server__applyLoop.lean  | 77 +++++++++++++++-------
 Spec/.../logkvcompact/Check.lean               |  5 +-
 Spec/.../logkvcompact/New.lean                 |  4 +-
 9 files changed, 124 insertions(+), 63 deletions(-)
```

Of the 1958 lines copied (Spec 344, Proof 1614), 9 files changed, 124 lines added and 63
removed. By cause (rough): the offset and compaction itself ~75 lines (`applyLoop` most of it,
`Defs`, `Put`'s append), the wrap-around bound ~35 (`Defs`, `Put`'s receipt, `New`, `Check`,
`Main`, specs and docs), the base's positional destructuring ~20 (`Get`, frame lists). Two specs
changed (`New`, `Check`: one premise each), none of `Put`/`Get`/`Apply`. Time: one sitting; every
proof went through on the first or second check after its edit.

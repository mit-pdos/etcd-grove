# etcd-io/raft#96: Optimise memory deallocation for stable log entries

- PR: https://github.com/etcd-io/raft/pull/96 (open, needs rebase), head
  `0e643b1b3eea6529572c08741f7ef920c13ba40d`, against upstream `main` at merge base `89c97ed7f`.
  It says it fixes etcd-io/raft#71 ("unstable can hold O(B log B) memory for a configured max B").
- Verified at the Goose fork commit `d22236cb2` (branch `pr-raft-96-goose-lean`, worktree
  `~/etcd-pr/raft-96`): the pinned raft base `509271dac` (raft v3.7, protobuf-go v2) plus the PR.
- Lean branch `pr-verify/raft-96` (worktree `/shared/etcd-grove-pr/raft-96`).
- Go probes: `notes/pr-verify/raft-96/` (README there).

## Verdict

The change is functionally safe. `unstable.stableTo`'s existing spec is re-proved, unchanged,
against the PR's code. The three new functions are proved with no `sorry`. The only trust-base
addition is the existing `proto.Size` postulate, which `stableTo` now reaches. No new axiom was
needed.

But the PR does not do what it says. The proofs cannot show this, because the model has no notion
of retained memory; the Go probes show it:

- It does not fix #71: the issue's sequence retains 162 MB with the PR, as before.
- It is a memory regression in other cases: an array with spare capacity that the old check copied
  out is now kept.
- It adds an O(len) loop over the unstable log, calling `Size()` on each entry, to every
  `stableTo` that leaves entries behind.

The reviewer of the PR (pav-kv) made the first point in 2023; the second and third are new here.

## Conflict resolution (verified code vs the PR)

One file, `log_unstable.go`; `git apply -3` conflicted in `stableTo` and `shrinkEntriesArray`.
Resolved in the base's style, with no behavior change beyond the PR:

- `stableTo(i, t uint64)` is `stableTo(id entryID)` on the base: `i` → `id.index`.
- Entries are `[]*pb.Entry` (protobuf-go v2): `make([]pb.Entry, n)` → `make([]*pb.Entry, n)`;
  gogoproto's `val.Size()` → `proto.Size(val)` (the same encoded size; the base's `entsSize` does
  the same).

`go build ./...` and `go test .` pass in the fork worktree. The PR adds no tests. The fork commit is
not pushed, so `etc/goose.py --check` fails on this branch, as expected.

## Changed functions

`go.etcd.io/raft/v3`, `log_unstable.go`. No type, field or package variable changes.

| Function | Kind | Before (`lean`) | After | Outcome |
|---|---|---|---|---|
| `unstable.stableTo` | refactor (the re-slice moved into the callee) | verified | verified | old spec re-proved unchanged (`Proof/go_etcd_io/raft/v3/unstable__stableTo.lean`) |
| `unstable.shrinkEntriesArray` | removed | verified | — | spec and proof deleted |
| `unstable.shrinkEntriesSlice` | new | — | verified | new spec |
| `unstable.doEntriesNeedCompaction` | new | — | verified | new spec (uses `proto.SizeEntry` postulate) |
| `unstable.compactEntriesSlice` | new | — | verified | new spec |

The specs are in `Spec/go_etcd_io/raft/v3/unstable__<fn>.lean`:

- `shrinkEntriesSlice(k)` and `compactEntriesSlice(k)`: given `0 ≤ k ≤ len(u.entries)`,
  `ownUnstable u us` becomes `ownUnstable u {us with ents := us.ents.drop k}`. `offset` is left to
  the caller, and the entries stay read-only.
  - The premise holds at the only call site: on a hit, `k = id.index + 1 - offset ∈ [1, len]`.
  - Outside the premise, the slice expression or the `make` would panic.
- `doEntriesNeedCompaction(k)`: for any `k`, it returns some `bool` and leaves the state unchanged.
  The answer is left unspecified for two reasons:
  - the capacity is not part of the state;
  - `proto.Size` returns some non-negative size, but no spec says which.

  Either answer is safe for the caller.
- The old `shrinkEntriesArray.spec` said "state unchanged", applied to a slice the caller had
  already cut. The new pair keeps the same overall effect inside `stableTo`, so the two specs agree.
  None of them can tell the PR's branches (nil / copy / re-slice) apart: they differ only in
  memory.

## Callers (step 6)

`unstable.stableTo`'s spec is unchanged, so the search stops there. Its caller
`raftLog.stableTo` and everything above it in `Link.lean` rebuild unchanged.
`shrinkEntriesSlice`, `doEntriesNeedCompaction` and `compactEntriesSlice` are only called from
the PR's own code (`grep` over the fork).

```
raftLog.stableTo  (unchanged spec, rebuilt)
└─ unstable.stableTo  (old spec re-proved)
   └─ shrinkEntriesSlice (new)
      ├─ doEntriesNeedCompaction (new) ─ proto.Size (existing postulate proto.SizeEntry)
      └─ compactEntriesSlice (new)
```

## Trust base (step 7)

The proof was checked with `lake build Proof.go_etcd_io.raft.v3.Link Proof.go_etcd_io.raft.v3.Results`
(1841 jobs, all of the raft tree rebuilt, since the translation changed). I did not run
`etc/tcb-report.py`: it needs a full `lake build`, including the server proofs that import raft.
Instead I compared `#print axioms` with the `lean` build:

- `unstable.wp_stableTo`, `raftLog.wp_stableTo` and `unstable.wp_shrinkEntriesSlice` (compared
  with the old `wp_shrinkEntriesArray`) gain exactly one axiom, `proto.SizeEntry.wp_proof`.
  - It is the existing trust-boundary spec of `proto.Size` on a `*pb.Entry`: some non-negative
    `int`, entry unchanged.
  - It is already in the `raft` collection, through `entsSize`/`limitSize`.
- Nothing was removed, and no `sorry` is reached.
- `compactEntriesSlice` rests on the same `make` model as the old `shrinkEntriesArray` did.
  `notes/bbolt-unsafe.md` gives the caveat that `wp_alloc` for arrays is proved by
  `wp_AngelicExit`.

The collection `etc/tcb-collections/pr-raft-96.txt` lists these roots, with the baseline written
from that comparison. Rerun `--check --update` after a full build. `etc/verified-code.py` was not
run, for the same reason. In counts, the package loses one verified function
(`shrinkEntriesArray`) and gains three.

## Findings

All three are about the PR. Reproductions are in `notes/pr-verify/raft-96/log_unstable_mem_test.go`,
with the results in `results.log`. They run against upstream: the PR head `0e643b1b3` and the base
`89c97ed7f`.

1. **It does not fix #71.** The issue's sequence is: 17×2 MB in a cap-32 array, then repeatedly
   append a larger entry and persist two. It ends with 162 MB retained, against at most 64 MB ever
   unstable, on both revisions.
   - Like the old check, the new heuristic reads `cap(u.entries)` of the current slice. That
     capacity ignores the prefix that earlier re-slices left behind in the backing array.
   - The two-sided bytes check only sees the visible entries.
   - This is pav-kv's review comment on the PR. #71's suggested fix is to track the full
     allocated size of the backing array.
2. **Memory regression.** Put 60 entries of 1 MB in an array of capacity 100, and persist the first 29.
   - Base: it re-slices to len 31 / cap 71, `2*31 < 71` holds, so it copies and 31 MB stay.
   - PR: `29 > 100/2` is false and `29 MB > 60 MB/2` is false, so it re-slices and 60 MB stay
     until a later compaction or reallocation.
   - The PR drops the old "remaining entries use less than half of the remaining capacity" test.
   - In fairness, the PR compacts in a case the old code never did: no spare capacity
     (`cap == len`) and more than half persisted.
3. **O(len) cost on partial `stableTo`.** `doEntriesNeedCompaction` sums `Size()` over every
   unstable entry, calling it twice per persisted entry. It does this whenever entries remain
   after the persisted prefix and the count test fails.
   - That happens when entries arrive between a `Ready` and its append response, and with
     `AsyncStorageWrites` it happens on every response but the last.
   - The common case (everything persisted) takes the `nil` branch and pays nothing.
   - Micro-benchmark, 10000 unstable entries, persisting one per call: about 1–1.6 µs/op on the
     base, 0.3–0.76 ms/op with the PR. This is an extreme case, not a production measurement.
     Persisting one entry at a time is quadratic overall.

None of these is a bug in the verified (pinned) code, so `issues/` has no new entry. The PR fixes
no finding recorded in `issues/`.

## Reviewer

A fresh reviewer subagent checked the specs, premises, ownership and aliasing, concurrency and the
conflict resolution. It found nothing blocking. Points it made:

- **Fixed.** A dangling line in `stableTo`'s doc listing.
- **Fixed.** The tie in the first version of probe 2: it persisted 30, so 30 MB was exactly half
  and the strict `>` decided it. Now 29.
- **Adopted.** State finding 3 as a worst case, not a production slowdown.

Notes from the review, not changes:

- Read-only entries (`entsRO`) still hold: no code writes an element of the old array.
  - This is also why the PR author's alternative in the review thread is unsafe: nil-ing out the
    persisted slots would write to an array that the application's `Ready` entries share.
- `proto.SizeEntry.spec` treats `Size` as a read. protobuf-go does write the message's size cache,
  atomically, into the hidden fields its invariant owns. The PR is the first to call
  `proto.Size` from `stableTo`.
- **Open (not done).** `InvRaftlog.lean`'s ownership comment still names `shrinkEntriesArray`
  first, as does an example in `notes/bbolt-unsafe.md`. Changing them would rebuild the whole raft
  tree for a doc comment.

## Draft review comment (for the user to edit and post)

> Thanks for working on this. I tried the change against the scenario in #71 and a couple of
> others (test file attached).
>
> - The #71 sequence (17×2 MB in a 32-slot array, then append-one/persist-two with growing
>   entries) still ends with ~162 MB held for ≤64 MB of unstable entries, same as `main`.
>   `cap(u.entries)` doesn't count the part of the backing array before the slice start, so the
>   new check has the same blind spot as the old one. I think #71 needs the full allocated size
>   tracked, as suggested there.
> - Dropping the old `len*2 < cap` check regresses some cases. With 60×1 MB entries in a 100-slot
>   array and 29 persisted, `main` copies the remaining 31 out (31 MB held), while this PR keeps
>   the array (60 MB).
> - `doEntriesNeedCompaction` calls `Size()` on every unstable entry on each `stableTo` that
>   doesn't persist everything. With 10k unstable entries persisted one at a time, `stableTo`
>   goes from ~1.5 µs to ~0.3–0.7 ms per call.
>
> Functionally the change looks right to me: the remaining entries are the same, nothing is
> mutated in place, and no index can go out of range. So the questions are only about the
> heuristic.

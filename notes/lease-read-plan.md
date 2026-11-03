# The lease read rows at the entry points: `LeaseTimeToLive`, `LeaseLeases` (2026-10-31)

Spec-first (`notes/spec-first-plan.md`). Item 2 of the lessor/auth list (the user: "start with 2",
after item 1, `notes/lease-revoke-plan.md`). Branch `lease-read`, worktree
`/shared/etcd-grove-leaseread`.

It reverses Part B's B4 ("the three checks only; the entry points stay names-only",
`notes/lease-keys-plan.md`) for the two read rows of `notes/auth-matrix.md`: `LeaseTimeToLive`
(admin, or read every key of the lease) and `LeaseLeases` (admin, or read every key of every
lease). `LeaseRenew` (the KeepAlive row) stays out (item 5).

## Scope (2026-10-31)

**The Go code** (etcd fork at the pin, `server/etcdserver/v3_server.go:607-790`,
`server/lease/{lessor,lease}.go`):

- `LeaseTimeToLive(ctx, r)`: `requireAuthInfo`; if `r.Keys`, `rev, err = checkLeaseTimeToLive`;
  `leaseTimeToLive(ctx, r)`; if `r.Keys` and auth is enabled, `ErrAuthOldRevision` unless
  `Revision()` is still `rev`.
- `leaseTimeToLive(ctx, r)`: on the leader, `waitAppliedIndex`, `lessor.Lookup(r.ID)` (again),
  `Remaining()` (the clock, under `l.expiryMu`), `TTL()`, `Keys()` if `r.Keys`, then
  `ErrLeaderChanged` if `Demoted()`; on a follower, a loop until the request's timeout:
  `waitLeader`, then `leasehttp.TimeToLiveHTTP` to each of the leader's peer URLs.
- `LeaseLeases(ctx, _)`: `lessor.Leases()` (the lease map's values under `le.mu`'s read lock,
  then `sort.Sort(leasesByExpiry(ls))`, whose `Less` compares `Remaining()`); `checkLeaseLeases`;
  the IDs and `newHeader()`.

**What exists**: proved, `checkLeaseTimeToLive`, `checkLeaseLeases` (each lease of its slice
`leaseLiveFrom`, a premise), `requireAuthInfo`, `isLeader`, `newHeader`, `AuthStore`,
`lessor.Lookup` and `Lease.Keys` from a reader (Part B), `Lease.TTL`; Perennial: `time.Until`,
`Time.IsZero`, `sort.Sort` (for a `Less` that agrees with a strict weak order). Names only: the
three entry points, `leaseTimeToLive`, `waitAppliedIndex`, `waitLeader`, `lessor.Leases`,
`Lease.Remaining`, `Lease.Demoted`, `leasesByExpiry`, `leasehttp` (all of it). At the server: one
lessor reader slot (`lessorRdOf`), the apply thread's; no request goroutine has one.

**S1. How much of `leaseTimeToLive`.** (a) The wrapper only: `LeaseTimeToLive` with its body,
`leaseTimeToLive` a trust-boundary contract that says nothing of the response (it may come from
another member's lessor). The spec states what was checked (the keys of the lease at a lessor
index `>= m`), the revision re-check, and nothing of the returned keys: the TOCTOU
(`issues/etcd-lease-timetolive-keys-toctou.md`) is the gap between them. (b) Also the leader's
branch with its body: the returned keys are the lease's keys at a later index `>= m'`, the
TOCTOU stated outright (two indices); it needs `waitAppliedIndex`, `Remaining`/`Demoted` from a
reader (a reader's access to `l.expiryMu`, which `isLeaseObj` does not give today: a definition
`Grant`'s proof and `Recover`'s axiom are written in), and the follower's branch stays a
contract (`waitLeader`, `TimeToLiveHTTP`). Recommended: (a); (b) later if wanted.

**S2. `lessor.Leases`' sort.** `Less` reads the clock, so it agrees with no fixed order, and
Perennial's `sort.Sort.spec` needs one. Go's `pdqsort` and its helpers guard every index by the
bounds, not by `Less`, so a `Less` that answers anything is safe and the result is a permutation.
(a) A clearly marked local trust-boundary axiom: `sort.Sort` for any `Less` (a triple that keeps
the sorter's resource), the result a permutation; and the general proof proposed to Perennial
(`notes/perennial-changes.md`), the axiom removed when it lands. (b) The Perennial change first,
`Leases` waiting for it. (c) `lessor.Leases` itself names-only, an axiom: each lease returned
live at an index `>= m`. Recommended: (a), the narrowest claim, about a library whose code
supports it.

**S3. Where the rows end.** The `EtcdServer` methods (recommended): their specs are what a
gRPC handler would call. Not `v3rpc`'s `LeaseServer` (names-only) nor a closed program.

**Server resources, for the Draft.** A request goroutine needs a lessor reader slot, a thread
token and a lessor lower bound at its start, as it has the auth store's `RD` today; the server
holds one slot only. The Draft designs the supply (a pool, like the auth store's readers).

**The user's decisions (2026-10-31).** S1: **the wrapper only** (`leaseTimeToLive` a contract).
S2: **a local axiom, and the general proof proposed to Perennial**. S3: **the `EtcdServer`
methods**.

## Draft (2026-10-31)

**Translation** (`etcd` project): `EtcdServer.LeaseTimeToLive`, `EtcdServer.LeaseLeases`
(`etcdserver.toml`); `lessor.Leases`, `lessor.unsafeLeases`, `leasesByExpiry` with `Len`, `Less`,
`Swap`, `Lease.Remaining` (`lease.toml`); the messages `LeaseTimeToLiveRequest`,
`LeaseLeasesResponse`, `LeaseStatus` (`etcdserverpb.toml`; until now axiomatized types).
`leaseTimeToLive` stays names-only.

**The specs** (statements; proofs in Prove):
- `EtcdServer.LeaseTimeToLive.spec` (`LeaseRead.lean` the vocabulary): on `nil`, the request
  authenticated (`authedOutB`) and, if `r.Keys`, `checkLeaseTimeToLive`'s class of the keys of
  `r.ID` at a lessor index `>= m`. **The margin, stated in the docstring**: those are the keys
  checked; the response is `leaseTimeToLive`'s, of which nothing is said (the TOCTOU). The
  revision re-check is not stated (item 3).
- `EtcdServer.leaseTimeToLive.spec`: **a new trust-boundary axiom** (the user's S1): with the
  request side's and the read side's server facts, its lessor, a lessor reader slot and a thread
  token, it returns, reading `r`; nothing of the response or error.
- `EtcdServer.LeaseLeases.spec`: on `nil`, the ids of the lease map at an index `i >= m`, all of
  it (`lease.leaseIdsAt`), the response listing them with a fresh header (`leasesRespIs`), and
  `checkLeaseLeases`' class of each lease's keys at an index `>= i`; on an error, no response,
  `applyErrIs`. (After the Review: the ids, not the leases' pointers; `i`, not `m`, for the keys.)
- `lease.lessor.Leases.spec` (a reader: `lessorRd`, `lessorLb m`, a thread token): a fresh slice
  of the lease map at an index `i >= m` (`leaseMapAt`), each lease `isLeaseObj` with its `ID`.
  `lessor.unsafeLeases.spec` (under the lock): the map's pairs, each id once.
- `leasesByExpiry.{Len,Less,Swap}.spec`, `Lease.Remaining.spec` (a thread token: some duration).
- `sort.Sort.anyLessSpec` (`Spec/sort/SortAnyLess.lean`): `sort.Sort` over a sorter whose `Less`
  answers anything (`sorterAnySpec`) ends a permutation. **A new trust-boundary axiom**,
  `sort.Sort.wp_anyLess` (the user's S2), its argument in the docstring (every index `pdqsort`
  passes to `Less`/`Swap` is bounded by the slice, not by `Less`'s answers).
- `EtcdServer.newHeader.spec` generalized from `isServerRead` to `isServerReadM on` (proved,
  no caller yet; the proof reads only the KV, read-view and term fields, the same in both modes).

**A definition grows** (`lease/InvLessor.lean`): `isLeaseObj γl l` gains `l.expiryMu`'s guard
(`leaseExpiry`, moved before it) and a pool of its reader slots (`leaseExpPoolN`), as Part B's
pool of `l.mu`'s: `Remaining()` on a gRPC goroutine borrows one with its thread token. `Grant`'s
proof gives the pool the slots it drops today. The axioms written in it (`NewLessor`, `Recover`,
`Promote`, `Demote`, `scheduleCheckpointIfNeeded`) create no lease (`Recover`'s model empties the
maps), so what they assert of it is unchanged; to confirm at the Probe.

**New vocabulary**: `lease.leaseMapAt`, `lease.leaseIdsAt` (with `leaseMapAt_live`, what
`checkLeaseLeases` takes, `leaseMapAt_perm`, for the sort, `leaseMapAt_ids`), `srvHeaderFacts`,
`srvHeaderAt`, `leasesRespIs`.

**Out**: the server-level supply of the request goroutine's lessor reader slot and thread token
(the specs take them, as the checks do); `LeaseRenew`; the revision re-check (item 3).

## Review (2026-10-31, `notes/spec-review/lease-read-draft.md`)

An independent review (the `spec-reviewer` agent, given the code, not the Draft's reasoning).
Applied:
- R1 (high): the contract axiom took `mvcc.txnCtx ctx cd`, which admits a context whose
  `Deadline()` panics; a follower's `context.WithTimeout(ctx, …)` calls it. Now `context.isContext`,
  in the contract and in `LeaseTimeToLive.spec`.
- R2: the contract now states what the code guarantees and the gRPC handler needs: on `nil` a fresh
  response with a header (`LeaseTimeToLiveResponse` now translated), on an error no response and
  `applyErrIs` (every error it returns is a package `errors.New`).
- R3: the contract's truth rests on the peers: a 200 reply without `LeaseTimeToLiveResponse` panics
  the follower (`leasehttp/http.go:274`). Reproduced (unit test) and filed:
  `issues/etcd-leasehttp-timetolive-nil-response-panic.md`; the contract's docstring states the
  assumption (the leader's peer URLs served by etcd's lease handler).
- R4: `LeaseTimeToLive.spec` gained the error arm (`resp = null`, `applyErrIs`), as `Range.spec`.
- R5: `LeaseLeases.spec`'s header premises bundled (`srvHeaderFacts`); its post states ids
  (`leaseIdsAt`), not the lessor's `*Lease` pointers.
- R6: the keys' index tied to the listing's: the keys checked at an index `>= i`, the listing's.
- R7: the Perennial note corrected: the general proof is not `wp_Sort`'s induction
  (`partialInsertionSort`'s left shift crosses the segment's start); the axiom is unaffected.
- R8: `Promote`'s header updated. Left: `leaseMeta` still carries the `expiryMu` guard (used under
  `le.mu` by `Grant` and `refresh`), and `srvHeaderAt` repeats `newHeader.spec`'s post.

The review confirmed: the sort axiom true of go1.27.3's `pdqsort`, as narrow as useful; the
`isLeaseObj` change sound (only `Grant` makes leases; `Recover`, `Promote`, `Demote` do not grow);
`newHeader`'s generalization; the lease package's specs. Not checked by it: that the contract's
server premises cover everything its body reads (`s.Cfg`, `s.cluster`, `s.peerRt`, `s.stopping`).

## Test (2026-10-31)

- The sort axiom against the real library (go1.27.3): `sort.Sort` with a random, an always-true, an
  always-false and a positional `Less`, sizes 0 to 100000, 20 seeds: 1200 sorts, no panic, each a
  permutation (a scratch test, not kept in the tree; its loop is in `Proof/sort/SortAnyLess.lean`'s
  header).
- etcd's tests at the pin pass: `tests/common` (`-tags integration`) `TestAuthLeaseTimeToLive`,
  `TestAuthLeaseLeases`, `TestAuthLeaseGrantLeases`, `TestAuthLeaseTimeToLiveExpired`,
  `TestLeaseGrantTimeToLive`; `tests/integration` `TestV3LeaseLeases`,
  `TestV3LeaseTimeToLiveWithLeaderChanged` (its subtests need gofail: 0.00s, not exercised);
  `tests/integration/clientv3/lease` `TestLeaseTimeToLive`, `TestLeaseLeases`,
  `TestLeaseTimeToLiveLeaseNotFound`.
- R3's panic reproduced (the issue's test).

## Probe (2026-10-31)

- **Easy: `Lease.Remaining`** (`Proof/.../lease/Lease__Remaining.lean`, 75 lines): borrow a slot of
  the lease's `expiryMu` pool (`isLeaseObj`'s new pool), read-lock, `IsZero`, `time.Until`, unlock,
  give the slot back. Checks clean; no surprise.
- **Hard: `lessor.Leases`** (`Proof/.../lease/lessor__Leases.lean`, 220 lines with its three lemmas):
  `lockHist_at` under the read lock for the index, the lock's `[∗map] isLeaseObj` and `leaseMeta`'s
  `ID ↦□` turned into the list's facts (`bigSepM_pairs`), `sort.Sort` with `sorterAnySpec` over the
  (pointer, id) pairs (`R l := sl ↦* l.map fst ∗ threadTok ∗ ⌜l.Perm ls⌝`, the `Members` template),
  `leaseMapAt_perm` for the sorted list. Builds.
- **Finding: the sort's `≤ 2^62`.** The axiom, like Perennial's `sort.Sort.spec`, takes at most
  `2^62` elements, and Go needs it (heapsort's `child := 2*root + 1` overflows past `2^62`); a slice
  in the model is only `< 2^63` and nothing bounded the lease map (a `Loc` is an unbounded `Int`, no
  address-space bound). Resolved without an axiom, by time receipts: `lessorMu` holds the persistent
  `⧖ |M|` (persistent, so it splits over the read lock's fractions, where `⧗ n` would not); `Grant`
  raises it at its insertion (`wp_raise_receipt`, at `leaseGranted.Inc`'s resolution, after a
  `wp_apply +noauto`), `Revoke` lowers it (`preceipt_mono`), the others keep it; `NewLessor` and
  `Recover` start at the empty map (`⧖ 0`, free: their axioms' text unchanged). So `|M| <
  receiptBound GF`, and `lessor.Leases.spec` and `LeaseLeases.spec` take `receiptBound GF ≤ 2^62`,
  as the closed results already do (`authkv`'s `MainServe`: `receiptBound GF ≤ 2^62`).
- **Cross-package unfolds:** none. The `Leases` proof unfolds only the lease package's own
  definitions (`lessorInv`, `lessorRd`, `lessorMu`, `lessorExtra`, `leaseMeta`, `leaseMapAt`); the
  etcdserver entry points will unfold `srvLessorRd`/`srvAuthLeaseLb` as `checkLease*` do.
- **Timings:** `lessor__Leases` 3.6s fresh in `lean-check`; `Lease__Remaining` under a second; the
  lessor proofs after `lessorMu`'s change: `Grant` 7s, `Revoke` 8s, as before.

## Freeze (2026-11-01)

The user: "approved, freeze and start Prove" (`notes/decisions.md`, "The lease read entry points").

## Prove (2026-11-01)

Proved, linked in the server's `Link.lean` (`etc/link-lean-first-server.txt`; `etc/gen-link.py`'s
`--server` imports `Proof.sort.SortAnyLess` for the `=` callee): `lease.Lease.Remaining`,
`lessor.unsafeLeases` (the map's range, as `Set.UnsortedList`), `leasesByExpiry.{Len,Less,Swap}`
(as `MembersByID`'s), `lessor.Leases`, `EtcdServer.LeaseTimeToLive` (its request split into fields
to read `Keys` and recombined, `typedPointsto_combine`, for the contract) and
`EtcdServer.LeaseLeases` (a local `leaseCheckFrom_mono`; `checkLeaseLeases` at the listing's
index). `lake build` passes; `etc/tcb-report.py --check` reports exactly the two approved axioms
(baseline and the `server` collection updated). Not linked from a gRPC entry point yet (the lease
server, `v3rpc`'s `LeaseServer`, is not in the link lists).

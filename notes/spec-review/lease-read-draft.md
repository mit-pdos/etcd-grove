# Review: the lease-read Draft (`notes/lease-read-plan.md`, "Draft")

Reviewer: independent spec review, 2026-10-31. Worktree `/shared/etcd-grove-leaseread`, branch
`lease-read`. The Draft is uncommitted, on top of `baaa2547dc`. Paths are relative to the worktree.
`srv/` means `Spec/go_etcd_io/etcd/server/v3/etcdserver/` and `lease/` means
`Spec/go_etcd_io/etcd/server/v3/lease/`. Go line numbers are at the etcd pin `249d76bea7`
(`.lake/go-src/etcd`) and at go1.27.3's `src/sort/zsortinterface.go`.

All the new Spec files, both new axiom files and `LeaseRead.lean` elaborate without errors
(`etc/lean-check.py -q`). I did not run `lake build`, the TCB report or the interface generator.

## Summary

The Draft holds together. The S1 margin (the TOCTOU) is stated where it belongs. `leaseMapFrom`
is the right new fact: the whole map, each id once, with the two laws the proof needs. The
`isLeaseObj` growth is sound. The `sort.Sort` axiom is true of go1.27.3's pdqsort. Two findings
must be fixed before Freeze, both in the new `leaseTimeToLive` contract axiom.

1. **High: the `leaseTimeToLive` axiom is false as stated** (soundness, hard rule). Its context
   premise is `mvcc.txnCtx ctx cd`, which admits a `doneNil` context, one known only to have a
   `nil` `Done()`. The follower path calls `context.WithTimeout(ctx, …)`, which calls
   `parent.Deadline()` first (`context.go:637`). The derived context then forwards `Value` to the
   parent, and the HTTP client calls `Value`. Under `doneNil` alone those methods can do anything,
   including panic. Fix: `context.isContext ctx cd`, which is what Range takes. The same change goes
   into `LeaseTimeToLive.spec`.
2. **Medium-high: the contract axiom states less than the code guarantees and less than the gRPC
   handler needs** (complete; the postcondition says what the caller inspects). On `nil` the code
   returns a non-null response with a non-null `Header`. On an error it returns `nil` and a
   package error variable (`applyErrIs`). `LeaseServer.LeaseTimeToLive` dereferences
   `resp.Header`, and `hdr.fill` panics on a nil header. It also calls `togRPCError(err)`. So
   `LeaseTimeToLive.spec` has no error arm, unlike `LeaseLeases.spec` and `Range.spec`. This
   axiom is being added now; strengthening it later would mean strengthening an axiom in place
   (`examples/watch-auth.md`).
3. **Medium: the contract's truth also rests on the peers, and the docstring does not say so.**
   On a follower, `TimeToLiveHTTP` dereferences `lresp.LeaseTimeToLiveResponse.ID`
   (`leasehttp/http.go:274`). A 200 reply whose body lacks that field (an empty body, say) is a
   nil-pointer panic in a gRPC handler goroutine, and etcd installs no recovery interceptor, so the
   process dies. A real etcd leader always sets the field (`http.go:131-138`). The axiom therefore
   holds only if every peer URL is served by etcd's leasehttp handler. Say so. This is also a
   robustness bug in Go, below.
4. **Medium: `LeaseTimeToLive.spec` has no error arm.** This follows from 2. Once the contract
   gives `resp = null ∧ applyErrIs err`, the spec can give the same disjunction as `LeaseLeases`.
5. **Low-medium: `LeaseLeases.spec` exposes internals.** Its precondition contains server field
   points-tos (`srvClusterAddr s ↦□ cl`, `membership.clusterCid cl cid`, `srvMemberIDAddr s ↦□ mid`,
   `srvLeadInv s`). Its postcondition contains the lessor's `*Lease` pointers (`ls : List (Loc ×
   w64)`). Separately, the map index and the keys' index are not tied together, although tying
   them costs only a re-binding.
6. **Low: the S2 note's claim about the Perennial proof is wrong.** The note says the any-`Less`
   proof is "the same induction as `wp_Sort` without the order". It is not:
   `partialInsertionSort`'s left shift runs `j >= 1`, not `j > a` (`zsortinterface.go:218`). With
   an arbitrary `Less` it moves elements below the segment, so `pdqsort.spec`'s `OutsideSame` is
   false. The axiom itself is unaffected, because it claims only a permutation of the whole list.
7. **Low: leftovers.** `leaseMeta` keeps a copy of the `expiryMu` guard, which `isLeaseObj` now
   carries. `lessor__Promote.lean`'s header says the reader slot is one "the lessor's invariant
   does not keep", which is stale now that each lease has a pool. `srvHeaderAt` restates
   `newHeader.spec`'s postcondition instead of `newHeader.spec` using it.

Ranked by need of revision: **`EtcdServer.leaseTimeToLive` (contract axiom) >
`EtcdServer.LeaseTimeToLive` > `EtcdServer.LeaseLeases` (with `LeaseRead.lean`) > `sort.Sort`
any-`Less` axiom (the notes only) > `isLeaseObj`/`leaseMapFrom` > `lessor.Leases` >
`newHeader` > `Lease.Remaining`, `leasesByExpiry.{Len,Less,Swap}`, `lessor.unsafeLeases`** (no
change needed for the last group).

---

## `EtcdServer.leaseTimeToLive.spec` and its axiom (`srv/EtcdServer__leaseTimeToLive.lean`, `Proof/.../EtcdServer__leaseTimeToLive.lean`)

### What is good

- It follows the user's S1 choice exactly: names only, with the docstring saying why nothing is
  claimed of the keys and pointing to the issue.
- The resources it hands back are the ones its callers need back: the lessor reader slot, the
  thread token and `r`.
- It returns `lessorRdOf γl ∗ threadTok`, which fits a leader-side `Lookup`, `Keys` (the `l.mu`
  pool) and `Demoted` (the new `expiryMu` pool). The new `isLeaseObj` gives the slot `Demoted()`
  needs (`lease.go:99-103`), so the leader branch is coherent with the vocabulary.
- It returns in the partial-correctness sense. The follower loop is bounded by `cctx` anyway
  (`v3_server.go:670-690`, with `waitLeader` returning on `ctx.Done()`).

### F1 (High, soundness): the context premise is too weak

- **Principle.** Sound (hard rule): a trust-boundary axiom must be true of the code under its
  premises.
- **Evidence.**
  - `mvcc.txnCtx ctx cd := doneNil ctx ∨ context.isContext ctx cd`
    (`Proof/go_etcd_io/etcd/server/v3/storage/mvcc/TxnRange.lean:99`). `doneNil` says only that
    `Done()` returns `nil` (`:90`).
  - The follower branch runs `context.WithTimeout(ctx, s.Cfg.ReqTimeout())` (`v3_server.go:670`).
    That calls `parent.Deadline()` before anything else (`context.go:637`). `propagateCancel`
    calls `parent.Done()` (`:479`). The derived `timerCtx` forwards `Value` to the parent, which
    `req.WithContext(cctx)` and the transport's lookups reach (`leasehttp/http.go:239-249`).
  - Under `doneNil` alone, `Deadline` and `Value` are unconstrained. A context type whose
    `Done()` returns `nil` and whose `Deadline()` panics satisfies the premise, and Go panics on
    it.
  - Perennial's `isContext` specifies `Deadline`, `Done`, `Err` and `Value`
    (`context/Base.lean:481ff`).
- **Caller affected.** `LeaseTimeToLive`'s proof applies this axiom. The axiom is also simply
  false of some instances its statement admits.
- **Restatement.** Replace `mvcc.txnCtx ctx cd` with `context.isContext ctx cd`, in this contract
  and in `LeaseTimeToLive.spec`. `Range.spec` already takes that, and a gRPC handler holds it.
  `isContext ⊢ txnCtx` is the right disjunct, so the checks' calls are unaffected and no caller
  loses anything. (`LeaseLeases.spec` may keep `txnCtx`: its only reader of `ctx` is the proved
  `checkLeaseLeases`.)

### F2 (Medium-high, completeness): the postcondition says nothing the handler inspects

- **Principle.** Complete (hard rule): sufficient for every caller, not only the one in mind. The
  postcondition says what the caller inspects. Also "Know the margin".
- **Evidence.**
  - `LeaseServer.LeaseTimeToLive` (`api/v3rpc/lease.go`) runs `resp, err :=
    ls.le.LeaseTimeToLive(..)`. Then `togRPCError(err)` unless `errors.Is(err, ErrLeaseNotFound)`.
    Then `ls.hdr.fill(resp.Header)`, which panics on a nil header (`api/v3rpc/header.go:54-55`)
    and writes the header's fields. That handler needs the following on `nil`: `resp ≠ null`,
    ownership of `resp`, and `resp.Header` non-null and owned. On an error it needs `applyErrIs
    err`.
  - What the Go code gives:
    - On the leader, a fresh response with `Header: &pb.ResponseHeader{}` (`v3_server.go:649`).
      Its errors are `waitAppliedIndex`'s (`ErrStopped`, `ErrTimeoutWaitAppliedIndex`,
      `v3_server.go:458-467`), `lease.ErrLeaseNotFound` and `ErrLeaderChanged`.
    - On a follower, a freshly unmarshalled response. Its `LeaseTimeToLiveResponse` is non-nil,
      because `http.go:274` dereferenced it. Its `Header` was sent non-nil by the leader
      (`http.go:133`). Its errors are `ErrNoLeader`, `ErrStopped`, `ErrLeaseNotFound` (returned as
      is from a 404, `http.go:261-263`), `ErrTimeout` and `ErrCanceled`.
    - Every error is a package `errors.New` variable, so `applyErrIs` holds
      (`apply/Base.lean:115-124`, `applyErrIs_leaf`).
- **Caller affected.** The gRPC handler, names-only today (S3). But this axiom is the only place
  that fact can come from. Strengthening a contract axiom later means strengthening in place and
  listing the collections (PRINCIPLES, hard rules; `examples/watch-auth.md`). It is cheaper to
  state it now, while the axiom is new and has no dependents.
- **Restatement.** Post: `lessorRdOf γl ∗ threadTok ∗ r ↦{dq} v ∗ ((⌜err = nil ∧ resp ≠ null⌝ ∗
  ∃ (rv : LeaseTimeToLiveResponse) (h : Loc) (hv : ResponseHeader), resp ↦ rv ∗ ⌜rv.Header' = h
  ∧ h ≠ null⌝ ∗ h ↦ hv) ∨ (⌜resp = null ∧ err ≠ nil⌝ ∗ applyErrIs err))`. Keep "nothing of the
  keys, `TTL`, `ID`" as the margin.

### F3 (Medium, soundness: an unstated assumption)

- **Principle.** Sound. A trust-boundary axiom is true of the code or of its documented behavior,
  so the environment it depends on must be named.
- **Evidence.** `TimeToLiveHTTP` (`leasehttp/http.go:224-277`) treats any 200 reply as a
  `LeaseInternalResponse`. An empty or foreign body unmarshals to a message whose
  `LeaseTimeToLiveResponse` is `nil`, and `:274` dereferences it. The panic is on the gRPC
  handler's goroutine. etcd's gRPC server has no recovery interceptor (none in
  `api/v3rpc/grpc.go` or `interceptor.go`), so the member crashes. etcd's own handler always sets
  the field (`http.go:131-138`).
- **Caller affected.** Everything resting on the axiom. It is true only if every peer URL of the
  leader is served by etcd's leasehttp handler: the cluster's members are etcd members and their
  advertised peer URLs reach them.
- **Restatement.** Add this to the docstring: "true only when the leader's peer URLs serve etcd's
  leasehttp handler (`http.go:274` dereferences the reply's `LeaseTimeToLiveResponse`, which etcd's
  handler always sets)". Check how the server's other peer-facing axioms state their peer
  assumption, and use the same wording.

**A Go bug (robustness).** The panic at `server/lease/leasehttp/http.go:274` is a candidate for
`issues/`. Reproducing it needs a peer URL that answers `POST /leases/internal` with 200 and an
empty body: a misconfigured or foreign peer, a version skew, or a proxy. I found no issue for it
(`grep -l leasehttp issues/` finds only the TOCTOU issue). I did not file one; this review is
read-only. `upstream: unchecked`. The fix is `lresp.GetLeaseTimeToLiveResponse() == nil` →
an error. The leader-side twin, `lreq.LeaseTimeToLiveRequest.ID` at `http.go:124`, only kills the
HTTP connection, because `net/http` recovers handler panics.

### Uncertain

- I did not check that `isServerReqM`/`isServerReadM` give everything the body reads: `s.Cfg`
  (`ReqTimeout`, `ElectionTicks`, `TickMs`), `s.cluster` non-nil, `s.peerRt`, `s.stopping`, and
  `ApplyWaitCommit`. An axiom can take more than it needs, but it must not be true only by luck.
  A sentence listing what the premises are for would let the Probe check it.

---

## `EtcdServer.LeaseTimeToLive.spec` (`srv/EtcdServer__LeaseTimeToLive.lean`)

### What is good

- It is true of the body (`v3_server.go:698-723`). On `nil`, `requireAuthInfo` passed, which
  gives `authedOutB … nil` (`EtcdServer__requireAuthInfo.lean`). If `r.Keys`,
  `checkLeaseTimeToLive` returned `nil`, which gives its `leaseCheckFrom …
  leaseKeysVerdictFrom` row.
- `if v.Keys'` is a case split on the input, which the principles allow, not a disjunction of
  alternative specs.
- **The margin is stated outright**: the keys checked are not the keys returned, with the issue
  linked. The revision re-check is named as omitted (item 3). This is the "Know the margin" rule
  done well.
- One spec in both auth modes (`E.authOn`, `E.authMode`).

### F4 (Medium): no error arm

- **Principle.** The postcondition says what the caller inspects, and siblings have the same
  shape (`Range.spec`, `LeaseLeases.spec`: `⌜resp = null ∧ err ≠ nil⌝ ∗ applyErrIs err`).
- **Evidence.** The post says nothing when `err ≠ nil`. The errors are `requireAuthInfo`'s,
  `checkLeaseTimeToLive`'s (`applyErrIs`, its post), `leaseTimeToLive`'s and
  `auth.ErrAuthOldRevision`. The error-returning paths all return `nil` responses
  (`v3_server.go:700-722`).
- **Caller affected.** The gRPC handler (`togRPCError`, `errors.Is(err, ErrLeaseNotFound)`).
- **Restatement.** After F2: `(⌜err = nil⌝ ∗ [as now] ∗ [the contract's response ownership]) ∨
  (⌜resp = null ∧ err ≠ nil⌝ ∗ applyErrIs err)`. This also needs `requireAuthInfo`'s error to be
  `applyErrIs`. Check whether `authedOutB` gives that on an error; if not, add the law there.
  Replace `mvcc.txnCtx` with `context.isContext` (F1).

---

## `EtcdServer.LeaseLeases.spec` (`srv/EtcdServer__LeaseLeases.lean`) and `LeaseRead.lean`

### What is good

- It is true of the body (`v3_server.go:737-749`). `Leases()`, then `checkLeaseLeases`, then the
  ids and `newHeader()`.
- The error arm matches `Range`'s: `applyErrIs` from `checkLeaseLeases`, with `resp = null`.
- `leaseMapFrom` is the whole map, each id once, which is stronger than "each listed lease was
  live". It makes the response a complete listing, and the order is honestly unspecified.
- `leasesRespIs` gives the caller what it inspects: the response, an owned header (`hdr.fill`
  writes it) and one `LeaseStatus` per lease, in order.
- The `newHeader` generalization (`isServerReadM on`) follows the rule that a mode is part of the
  state. Its proof only renames the unfold (`EtcdServer__newHeader.lean` diff). It has no other
  callers (`Link.lean:2397` is the only use), and `isServerReadM_false` (`ReadOn.lean:104`) keeps
  the off instance `rfl`.

### F5 (Low-medium, abstraction): field points-tos in the precondition, `*Lease` pointers in the postcondition

- **Principle.** "The spec of an API, not of an implementation" (no internal fields). "The
  vocabulary is part of the spec". Size.
- **Evidence.**
  - The precondition carries `srvClusterAddr s ↦□ cl ∗ membership.clusterCid cl cid ∗
    srvMemberIDAddr s ↦□ mid ∗ srvLeadInv s`, which are `newHeader.spec`'s raw facts. It is the
    first entry point to take them; `Range.spec` takes none.
  - The postcondition's `ls : List (Loc × w64)` puts the lessor's `*Lease` addresses into an
    `EtcdServer` API, though the response carries only ids. A single in-memory server would have
    no such pointers.
- **Callers affected.** A future handler or closed-program proof, which must supply four field
  facts and carry `Loc`s it never uses.
- **Restatement.**
  - Bundle the header facts: `srvHeaderIds s cid mid := ∃ cl, srvClusterAddr s ↦□ cl ∗
    clusterCid cl cid ∗ srvMemberIDAddr s ↦□ mid ∗ srvLeadInv s` (persistent, produced where
    `NewServer` produces them). Use it in `newHeader.spec` too.
  - Optionally, hide the pointers: `∃ ids, lease.leaseIdsFrom γl m ids ∗ leasesRespIs E resp cid
    mid ids ∗ leaseCheckFrom … (fun info => [∗list] id ∈ ids, ∃ l, leaseLiveFrom γl m id l ∗
    leaseOfKeysVerdictFrom … id l .read)`, with `leaseIdsFrom` the id-level `leaseMapFrom`. I
    rank the pointer hiding as optional, because `leaseOfKeysVerdictFrom` is pointer-indexed
    already in the proved check spec.

### F6 (Low, strength): the map index and the keys' index are not tied

- **Principle.** "Facts that can be combined".
- **Evidence.** The postcondition gives the map at some `i ≥ m` (`leaseMapFrom γl m ls`) and the
  keys' verdicts at some `j ≥ m` (`leaseOfKeysVerdictFrom … m`). The code reads the keys after
  taking the map. The proof can rebind `m := i`: `leaseMapFrom γl m ls ⊢ ∃ i, ⌜m ≤ i⌝ ∗
  leaseMapFrom γl i ls` holds by definition (`InvLessor.lean:407`). It can then call
  `checkLeaseLeases` at `i` and get `j ≥ i`.
- **Restatement.** `∃ i, ⌜m ≤ i⌝ ∗ leaseMapFrom γl i ls ∗ … leaseOfKeysVerdictFrom … γl i x.2
  x.1 .read`. It is stronger and costs nothing. Take it only if a client needs the order; otherwise
  name it in the docstring as the margin.

### Small points

- `LeaseRead.lean`'s header lists `leasesRespIs resp ls`. The definition takes `E resp cid mid
  ls`.
- `srvHeaderAt` repeats `newHeader.spec`'s postcondition word for word. Restate
  `newHeader.spec`'s postcondition with it (moving it to where `newHeader.spec` can import it),
  so that the two cannot drift.

---

## `sort.Sort.anyLessSpec` and `sort.Sort.wp_anyLess` (`Spec/sort/SortAnyLess.lean`, `Proof/sort/SortAnyLess.lean`)

### Is it true of Go's `sort.Sort`? Yes

I read go1.27.3's `sort.go:50-57` and `zsortinterface.go:9-327`. Every index passed to
`Less`/`Swap` lies in `[0, n)` whatever `Less` answers:

- `insertionSort`: `j > a`.
- `siftDown`: `child >= hi` breaks, and `child+1 < hi`.
- `heapSort`: `first + [0, hi)`.
- `partition` and `partitionEqual`: guarded by `i <= j` in `[a+1, b-1]`. Every `Swap(j, a)` has
  `j ≥ a`.
- `partialInsertionSort`: `i < b`, `j >= 1`, `j < b`.
- `breakPatterns`: `idx ∈ [a + length/2 - 1, a + length/2 + 1]`, `other < length`.
- `choosePivot`, `median`, `medianAdjacent`: `a ± 1` with `l ≥ 50`.
- `reverseRange`: `i < j`.
- `pdqsort`'s `a-1`: only under `a > 0`.

Other conditions:

- **Termination and stack.** It terminates, though partial correctness does not need it. Each
  loop pass returns or shrinks `[a, b)`: `partitionEqual` returns `i ≥ a+1`, and `partition`'s
  `mid ∈ [a, b-1]` is excluded from both halves. The recursion goes into the smaller half
  (`< length/2`), so the depth is at most about 62.
- **Overflow.** Under `n ≤ 2^62` there is none (`2*root+1`, `first+child+1`).
- **Permutation.** Only `Swap` writes. Given the `Swap` triple, the result is a permutation.

### Is it narrow? Mostly

- The claim is the permutation only, which is all the code gives. The premises are
  `sorterSpec`'s with `Less`'s answer free, and the same `2^62` bound as `sort.Sort.spec`.
- Being generic over `E` and `R` is right. It lets `Leases`' proof sort pairs `(l, id)`, which it
  needs: from `leaseMapFrom` alone the `*Lease` pointers are not known distinct, so permuting the
  bare `Loc`s and rebuilding the pairs would not go through.
- It is not stronger than Perennial's proved `sort.Sort.spec` anywhere both apply, and it is
  consistent with it.
- A narrower variant specialized to `leasesByExpiry` would buy nothing. The general claim is true
  of the library and is what the proposed Perennial change would prove.
- The section fixes `HeapGS HasLC.hasLC GF`, where `Spec/sort/Sort.lean` is generic over `hlc`.
  That is harmless, but differs from its sibling.

### F7 (Low): the proposed Perennial proof is not "the same induction"

- **Evidence.** `notes/perennial-changes.md` (new entry) and the plan say the general proof is
  "the same induction as `wp_Sort` without the order".
  - Perennial's `sort.pdqsort.spec` keeps `OutsideSame xs xs' a b` and a `header R xs a b`
    precondition (`Perennial/Spec/sort/pdqsort.lean`).
  - With an arbitrary `Less`, `partialInsertionSort`'s left shift (`zsortinterface.go:217-224`,
    `for j := i - 1; j >= 1; j--`) runs past `a` down to index `1`, swapping elements below the
    segment. `pdqsort` calls it on segments with `a > 0` (`:100-104`, in the loop after a
    recursion).
  - So the segment-local invariant is false for an arbitrary `Less`. The general proof needs a
    whole-slice invariant: indices in `[0, n)`, a permutation of the whole list.
- **Restatement.** In the docstring and the note: "elements outside the segment may move (the
  left shift of `partialInsertionSort` stops at index 1, not at `a`), so only the whole list is a
  permutation. The proposed proof keeps indices in `[0, n)` rather than `OutsideSame`." The axiom
  needs no change.

---

## `isLeaseObj` (grown) and `leaseMapFrom` (`Proof/go_etcd_io/etcd/server/v3/lease/InvLessor.lean`)

### What is good

- The growth is sound and minimal. It adds the persistent guard of `expiryMu` over `leaseExpiry`,
  which `leaseMeta` already carried (`:561-567`), and a pool of its reader slots, guarded by the
  same `threadBound` premise as Part B's `l.mu` pool.
- `Remaining()` and `Demoted()` take only `RLock` (`lease.go:99-124`). The writers `refresh` and
  `forever` take the guard alone (`lease/Lease__refresh.lean`, `Lease__forever.lean`, via
  `wp_Lock_guard`). So the pool is exactly what a reader on a goroutine needs.
- `Grant` is the only producer of `isLeaseObj`. Today it drops the slots it gets from
  `init_RWMutex` (`lessor__Grant.lean:115-121`), so the pool can be built from them.
- The plan's claim that the axioms written in `isLeaseObj` create no lease checks out for
  `Recover`. Its precondition is an empty lease bucket and its postcondition is `leaseOwn γl [] ∅`
  (`lease/lessor__Recover.lean`). `Promote` and `Demote` only keep the map's (persistent)
  `isLeaseObj`. So no axiom's claim grows.
- `leaseMapFrom` is persistent, and its two laws (`_live`, `_perm`) are the ones `LeaseLeases`'
  and `Leases`' proofs need. The `Nodup` of ids is stated, not left to a client to derive.

### F8 (Low): leftovers after the change

- `leaseMeta`'s `isRWMutexGuard (expiryMu) (leaseExpiry l)` (`:567`) is now redundant: every
  lease of `lessorMu`'s map has `isLeaseObj`, which holds it. Drop it, per "After a change, drop
  what existed only for what it changed", if no proof needs it from `leaseMeta` specifically.
- `Proof/.../lease/lessor__Promote.lean:4-5` says `Remaining()`'s slot is one "the lessor's
  invariant does not keep". That is no longer so; update the sentence. (`Promote` stays
  names-only for its float conversion.)
- Grant can put every one of the `actualMaxReaders` slots into the pool (`ownRWMutex_guard` keeps
  the guard), not "all but one". This is immaterial while the `2^30 - 1` bound comes from the
  `l.mu` pool.

---

## `lessor.Leases.spec`, `lessor.unsafeLeases.spec` (`lease/`)

### What is good

- Both are true of `lessor.go:464-478`. `unsafeLeases` ranges over the map under the caller's
  read share and appends to a fresh slice, giving each pair once. `Leases` reads under `RLock`,
  releases it, then sorts. Taking the lessor reader slot, a lower bound `m` and a thread token
  matches `Lookup`'s reader shape.
- The postcondition's `lsF go!"ID" x.1 ↦□ x.2` is what `LeaseLeases` reads (`ls[i].ID`, a field
  access). It is obtainable inside the lock from `leaseMeta` (persistent, `InvLessor.lean:562`).
- `Leases()` has one caller (`v3_server.go:738`; `Promote` uses `unsafeLeases` plus the sort
  under its own lock). The spec fits that caller with `leaseMapFrom_live` and nothing else.

No findings.

## `Lease.Remaining.spec`, `leasesByExpiry.{Len,Less,Swap}.spec` (`lease/`)

### What is good

- They are true of `lease.go:117-135`:
  - `Remaining`: `expiryMu.RLock`, `IsZero`, then `time.Until` or `MaxInt64`. There is no panic.
  - `Less`: two `Remaining()`s on in-range indices.
  - `Swap`: `le[i], le[j] = le[j], le[i]`, which gives `set i b` then `set j a`, correct when
    `i = j` too.
  - `Len`: `len(le)`.
- `Less` and `Swap` take the index premises in exactly `sorterAnySpec`'s form, so the sorter
  triple is a direct instance.
- `Remaining` claims nothing about the duration, and says why (the clock and `refresh`).

No findings. (`Less` and `Remaining` rely on `isLeaseObj` being persistent for not returning it,
which holds: `isLeaseObj_persistent`.)

---

## Process notes

- There are two new axioms, `sort.Sort.wp_anyLess` and `EtcdServer.leaseTimeToLive.wp_proof`.
  `etc/tcb-baseline.txt` and the collections that reach `LeaseLeases`/`LeaseTimeToLive` need
  `--check --update` at Prove, and the plan's "Out" should list the axioms as such.
- Only raft has an `etc/api` list, so no `interface/` file moves.

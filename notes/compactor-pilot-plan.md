# Plan: the spec-first pilot, etcd's auto-compactor

Status: phase 0 done (2026-10-27, branch `compactor-pilot`): this note is phase 0's output, the
scope and the top-level statements. Scope **(A)**, the compactor and the server's compaction path
(the user, 2026-10-27). Next: phase 1.
Step 3 of `notes/spec-first-plan.md` ("Testing the plan").

## What the pilot is

Verify `server/etcdserver/api/v3compactor` (the auto-compactor: `compactor.go`, `periodic.go`,
`revision.go`; 14 functions, about 340 Go lines, 0% verified) spec-first, in the plan's phases (0
scope, 1 the spec skeleton and the glue proofs, 2 testing the specs against Go, 3 one full proof,
freeze, 4 the remaining proofs), and measure it against the read-index loop
(`server/etcdserver/read`, 10 functions, 178 lines), done the current way. Main metric: spec
revisions after the freeze, classified with step 1's rubric (success: at most 2 that are not INFRA,
none FALSE-BEH).

## What the proofs assume today

- `NewServer`'s premises have the compactor off: `AutoCompactionRetention = 0`
  (`examples/common/common.go:68`, every example's configuration). etcd's default is also off
  (`embed/config.go:71-72`: mode `periodic`, retention `"0"`).
- `v3compactor.New` is a trust-boundary axiom whose post is `True`
  (`Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3compactor/New.lean`, with the premise
  `ret ≤ -10 ∨ 10 ≤ ret` from `issues/etcd-compactor-periodic-tiny-retention.md`); the server's
  `run` sees the compactor only through `compactorOk` (`InvRun.lean`: nil, or `Pause`/`Resume`
  return), a names-only contract.
- **Compaction requests are outside the server's model**: `apply.dispatchOk` requires
  `dispatchKind rq ≠ .compaction` (`apply/InvUber.lean`; `notes/decisions.md`, "The server's apply:
  ... compaction out of the model", 2026-10-12), and `plainReq` admits no compaction
  (`KVModelDefs.lean`, `putgetKind`). mvcc's compaction itself is specified and proved
  (`store.Compact` and below, collection `mvcc-compaction`), under the premise `NoDelPutAt`; the
  client-facing `KVState` has a `compacted` revision already.

So turning the compactor on is not a 14-function change: its `Compact` calls go to
`EtcdServer.Compact` (`v3_server.go:382`), which proposes `InternalRaftRequest{Compaction}`
through raft, and every member applies it (`applierV3backend.Compaction`, `apply/backend.go:66`,
over mvcc's `store.Compact`). That is the first thing phase 0 found.

## The configuration (fixed now)

- Both modes, as etcd accepts them (`embed/etcd.go:928`, `parseCompactionRetention`): `periodic`
  with a retention duration (an integer means hours, e.g. `1`, the documented example; or a
  duration, `10m`), and `revision` with a revision count (`1000`, the documented example).
- Premise for `periodic`: a retention of at least 10ns (below, `getRetryInterval` is 0 and `New`
  divides by zero: `issues/etcd-compactor-periodic-tiny-retention.md`; etcd accepts it).
- The compactor runs on every member; `run` pauses it on a follower and resumes it on the leader
  (`server.go:762-785`). It starts in `NewServer`, before `Start`
  (`issues/etcd-compactor-started-before-start.md`): `Compact`'s contract must hold from then on.
- Other compactions (a client's `Compact`) stay out of the pilot's workload; the examples issue none.

## The top-level statements (drafts)

**C1, the compactor's guarantee** (the property operators configure it for: history is kept for the
retention). Every `CompactionRequest` the compactor sends has a revision `r` with `0 < r`, and:
- `revision` mode: `r + retention ≤ σ.rev` at the call (`r = Rev() - retention`, read before the
  call; the store's revision only grows);
- `periodic` mode: `r` is a revision the store had at a clock time at least
  `⌊period / retry⌋ · retry` before the call (`retry = min(period, 1h) / 10`; `revs[0]` was
  sampled `retentions - 1` iterations ago, each iteration waiting `retry` on the clock), so
  `r ≤ rev(now - ⌊period/retry⌋·retry)`;
- its requests' revisions never decrease (`Rev()` is monotone, and the periodic window only slides).

Not in C1: "no request after `Stop`". `Stop` only cancels the context, so a call in flight still
completes (with the context canceled). Phase 2 checks what `Stop` does guarantee.

The clock is a trust boundary (`clockwork.Clock`: `Now` monotone in the real clock's monotonic
reading, `After(d)` fires no earlier than `d`); phase 1 states it, phase 2 tests it.

**C2, the server with auto-compaction on** (option A only). The examples' closed theorems hold
when the server runs with auto-compaction on, in either mode, for any accepted retention: starting
with `putget_safe` (`examples/putget`), whose workload (puts and latest reads) never reads a
compacted revision; then the others. With compaction in the model, `KVState.compacted` advances at
a compaction's apply, reads below it answer `ErrCompacted` (the model has the field already).
Premise: the workload meets `NoDelPutAt` (no transaction deletes a key from-key and puts it again:
`issues/etcd-compaction-delete-then-put.md`, now reachable through auto-compaction alone; putget's
workload meets it trivially), until the fix (etcd-io/etcd#22377) is in the fork.

**C3, C1 in the KV model** (option A only): `σ.compacted ≤` the revision `C1` allows, for every
state the server reaches, given that only the compactor compacts. This is what a client relying on
the retention (a watch resuming within it) needs.

## The scope decision (the user's: (A), 2026-10-27)

- **(A) The compactor and the server's compaction path** (recommended): the 14 compactor functions;
  `EtcdServer.Compact`; `applierV3backend.Compaction` and the dispatch's compaction arm (the
  `dispatchOk` premise lifted for compactions); the KV model's compaction step and the server's
  invariants with compactions applied; `NewServer`'s `AutoCompactionRetention = 0` premise and the
  `New` axiom and `compactorOk` replaced; C1, C2 (putget first), C3. About 20 Go functions plus the
  model work. It is the plan's phase 0 doing its job: decided now, not found as a scope extension
  in phase 4 (step 1: 20 of 64 spec revisions were scope extensions).
- **(B) The compactor alone**: the 14 functions against a trust-boundary contract for its
  `Compactable` (an axiom on `EtcdServer.Compact`); C1 only; the server keeps auto-compaction off.
  Comparable in size to the read-index loop, so the cleaner experiment; but it narrows the scope the
  plan says to fix up front, and the axiom is exactly what a later widening would have to replace
  (with a re-proof of C1's callers).

Under (A) the pilot is larger than the baseline; the comparison then normalizes by functions and
Go lines, and counts the server-side spec revisions separately from the compactor's.

## Phase 1, once the scope is chosen

Write every spec of the chosen scope (the compactor's 14; the clock's; under (A) `Compact`'s,
`Compaction`'s, the dispatch arm's, the model step), proofs `sorry`; generate the links; prove the
glue: `New`'s dispatch, `NewServer` and `run` over `New.spec` (the compactor's goroutine's
proposals with `Compact`'s contract before `Start`), and under (A) `EtcdServer.Compact` over
`processInternalRaftRequestOnce`. Record the freeze candidates' state for phase 2.

## Phase 1: the design of the skeleton (2026-10-27)

**Translation (done).** `v3compactor` with bodies (`Code/.../api/v3compactor.toml`, all 14
functions, no axiom left); `EtcdServer.Compact` with its body (`etcdserver.toml`);
`github.com/jonboulle/clockwork` names only (a new package of the `etcd` project: its `-lean-root`
and owned path in `etc/goose.py`; `Clock` is axiomatized by Goose, the compactor only calls its
methods through the interface); the apply package's `applierV3backend.Compaction` was translated
already. Initializers regenerated (`etc/gen-init.py`; clockwork's `IsPkgInit` in `BaseApply.lean`,
before `v3compactor`'s, which now imports it).

**The compactor's environment as contracts** (persistent, as `compactorOk` is for the server):
- `revGetterOk rg γ`: `rg.Rev()` returns `v` with `idxCert γ.idx log` and `v = |log| - 1` (what
  `mvcc.store.Rev` gives; the server passes `srv.kv`): a revision lower bound that only grows.
- `compactableOk c P`: for every `r` with `P r`, `c.Compact(ctx, &CompactionRequest{Revision: r})`
  returns. `P` is the permit the compactor's proof must establish at each call: **C1 is `P`.**
- `clockOk clk γc` (trust boundary, `clockwork.NewRealClock`): `Now()` returns `t` with `clockLb γc
  t` (the clock is at least `t`, persistent); `After(d)` returns a channel whose value comes once the
  clock is at least the clock at the call plus `d`. The clock is a ghost monotone counter in an
  invariant (`clockInv γc`), advanced only by the environment: the trust boundary is that real time
  is monotone and `After` does not fire early (clockwork's real clock uses Go's monotonic reading).

**C1 as permits.**
- revision mode: `P r := 0 < r ∧ revLb γ (r + retention)` (`revLb` from `idxCert`).
- periodic mode: `P r := 0 < r ∧ ∃ T, revLbBy γ γc r T ∗ clockLb γc (T + K)` with
  `K = ⌊period / retry⌋ · retry`: the store's revision was at least `r` by clock time `T`, and the
  clock is now past `T + K`. `revLbBy` is a persistent fact stamped from a `revLb` and a clock
  reading taken after it (`stamp`: `revLb γ r ∗ clockNow γc t ⊢ revLbBy γ γc r t`, at an atomic
  clock step; the `After` call after each `Rev()` sample is that step). The loop invariant of
  `Periodic.Run`: each `revs[i]` has its stamp `Tᵢ`, and the clock is past
  `Tᵢ + (len - 1 - i) · retry`.

**The server side.**
- `putgetKind` (or its successor) admits `.compaction`; `dispatchOk` stops excluding it; the KV
  model's compaction step (`KVState.compacted := r`, the base and changes re-cut) at the apply of a
  `Compaction` request; `applierV3backend.Compaction` over mvcc's `store.Compact` (which needs
  `NoDelPutAt`, the workload premise).
- `reqPropOk`'s compaction form: a compaction at `r ≤` a revision the proposer has seen
  (`idxCert`); the compactor's `P r` implies it in both modes.
- `EtcdServer.Compact.spec` over `processInternalRaftRequestOnce` (glue), from `NewServer` on
  (the compactor runs before `Start`: `issues/etcd-compactor-started-before-start.md`); its
  `Physc` wait only when `r.Physical` (the compactor never sets it).
- `NewServer`: the premise `AutoCompactionRetention = 0` replaced by the mode/retention premises;
  `compactorOk` derived from `New.spec` instead of assumed.

**Glue proofs of phase 1:** `New` (the mode dispatch, `newPeriodic`, `newRevision`, the getters),
`EtcdServer.Compact`, and `NewServer`/`run` over the new contracts. `Periodic.Run` and
`Revision.Run` are phase 3's full proofs (`Periodic.Run` first, the riskiest), `sorry` until then.

## Phase 1, step 2: the specs (2026-10-27)

**Written** (all check; proofs `sorry` unless said):
- the clock's trust boundary: `Proof/github_com/jonboulle/clockwork/Defs.lean` (axiomatized
  `clockLb`, `stampAt`, `realClock`; `clockOk`), `clockwork.NewRealClock.spec` (an axiom);
- the compactor's vocabulary, `Proof/.../api/v3compactor/Defs.lean`: `revLb`, `revGetterOk`,
  `compactReqIs`, `compactableOk c P R`, C1's `revPermit`/`perPermit`/`modePermit`, `CompactEnv`,
  `isPeriodic`/`periodicRunTok`, `isRevision`, `compactorOk cp RunTok R`;
- the 14 compactor specs (`Spec/.../api/v3compactor/`), `New.spec` restated (the axiom with post
  `True` is gone: `New.wp_proof` is a `sorry` until the glue);
- `EtcdServer.Compact.spec` (over `isServerReq`, at a revision the store has reached), and the
  getters `CompactionRequest.GetPhysical`/`GetRevision` (translated now, proved);
- the server's link list (`etc/link-lean-first-server.txt`) and `Link.lean`.

**What writing the specs changed** (the pilot counts these: changes to phase 0's statements and to
phase 1's design, before any proof):
1. **C1 restated for the periodic mode.** A compaction's revision is the window's oldest sample,
   which the code never stamps with a clock reading: it reads the clock (`Now`) before the first
   sample, and compares elapsed times with `Time.Sub`, which Perennial specifies as returning any
   duration. With a full window the bound comes from the `After` waits since the sample (each at
   least `retry`: `stampAt`, taken at the `After` call after the sample). The run's first
   compaction has no such bound: its sample is the run's first, taken some time after `start`, and
   only `now - start ≥ period` is known; a scheduling delay between `Now()` and the first `Rev()`
   would let it compact a revision younger than the retention. `perPermit` says exactly that (its
   second disjunct). Real delays are milliseconds, so no `issues/` entry; the statement records it.
2. **`Compactable` threads a resource `R`.** The server's proposal path consumes per-thread pieces
   (a reader slot `E.RD`, `srvLeadTimeReader`); the compactor's goroutine holds them across its
   calls (`compactableOk c P R`, `R` given to `Run`). Request ids are minted from the server's
   persistent `□ |==> idCred ρ.ids 1`.
3. **Before `Start`.** `Compact`'s proof needs `isServerReq`, which the proofs establish in `Start`,
   but the compactor runs from `NewServer` on (`issues/etcd-compactor-started-before-start.md`).
   The glue for `NewServer` must give the compactor a `Compact` contract before `Start`: either an
   `isServerReq` established in `NewServer`, or a contract whose resource waits for `Start`. Open.
4. **Two more translated functions**: `Compact` reads `r.GetPhysical()`/`r.GetRevision()` for its
   trace span (`etcdserverpb.toml`).
5. **Merging.** `New`'s proof builds the `Run` contract (`compactorOk`), so it takes
   `Periodic.Run.spec` as a hypothesis, and every closed theorem through `NewServer` would reach
   `Run`'s `sorry` even with auto-compaction off. The pilot's specs stay on branch
   `compactor-pilot` (with `lean` merged in) until the compactor's proofs are done; the
   translation (step 1) is merged.

**Step 2b, the review** (added 2026-10-27: `notes/spec-first-plan.md`, "Phase 1b"): before the
glue, a fresh reviewer ranks the specs that cross a package boundary (`New`, `compactorOk`, the
environment's contracts and C1's permits, the clock's, `EtcdServer.Compact`) in the two tiers;
steps 2 and 3 then alternate per boundary until the freeze. Self-review before it, by the rubric,
already found: `EtcdServer.Compact`'s post gives nothing, which its other caller (the gRPC
`kvServer.Compact`, whose `compactOk` needs a response header) cannot use, and its premise `revLb r`
excludes clients that compact a future revision (Go answers `ErrFutureRev`); `revGetterOk` ties the
compactor to mvcc's `idxCert` where any monotone lower bound would do; `perPermit` fixes the window's
exact age where a simpler bound may be all C3 needs.

**Step 2b, round 1: the findings and the repairs** (the report:
`notes/spec-first-study/pilot-review-1.md`; the author's self-review had found 4 of them):

| finding (reviewer's rank) | tier | repair |
|---|---|---|
| `Compact`'s post gives nothing; the gRPC caller needs a header, the compactor an `errors.Is`-able error | requirement | `compactOutIs`: `nil` and a response with a header at a reached revision, or `applyErrIs err` |
| `Compact`'s premise `revLb r`: a future revision is legitimate (`ErrFutureRev`) | requirement | dropped |
| `Compact` auth-off only | requirement | `Compact.specOn` (`isServerReqM true`) |
| `Compact` reads `s.kv.Rev()`: needs the store's reader slot | requirement | `mvcc.storeReader` in its pre and post |
| `Compact`'s `Physical` true (the gRPC caller's) | requirement | kept out, stated as scope: the physical wait is not specified yet |
| `revGetterOk` resource-free, but `store.Rev` needs a reader slot | requirement | threads the resource `R` |
| `compactableOk`'s post ignores the result | requirement | returns the pair and `errTreeOk err` (Perennial's error-tree fact: the part of `applyErrIs` the compactor needs) |
| periodic `0 < r` unprovable (`revLb v` for `v ≤ 0`) | requirement | `revGetterOk` gives `0 ≤ v`; `Run` skips `rev = 0` |
| **`perPermit` vacuous** (its weak disjunct always holds) | requirement | restated (the user's choice): `period` old, except the run's first compaction, `retry` old, consuming a once-per-run token `First` the server gives `Run` |
| the clock's `After` cannot chain bounds | requirement | `After` gives `T ≥ n` for a bound `n` the caller holds; `clockLb_init` (the user approved the trust-boundary change) |
| `After`'s premise `0 ≤ d` (Go accepts any) | requirement | dropped |
| the clock axioms have a trivial model | (documentation) | the docstring says how results over them read |
| coupling to mvcc's `IdxNames` | preference | `CompactEnv.RevLb`, an abstract lower bound (the server's is `revLb`) |
| `periodK` one `retry` short, and not needed | preference | gone (the permit uses `period`) |
| `New`'s `10 ≤ ret` stricter than the code | requirement | kept as the pilot's configuration (phase 0), cited in the docstring |
| name clash with the server's `compactorOk` | preference | left for the glue (the server's becomes a corollary) |

**Step 2b, round 2: the findings and the repairs** (`notes/spec-first-study/pilot-review-2.md`; two
of its three blockers came from round 1's repairs; one finding a false positive):

| finding | repair |
|---|---|
| the token `First` is spent by a retried first compaction (`periodic.go`: a failed `Compact` leaves `lastRevision` and retries the same sample) | the young case depends on the revision: `firstSample γf r`, a ghost variable set once to the run's first sample (`runPre`'s `firstUnset`); C1: at most one *revision* per run younger than the period (the user's choice) |
| periodic `0 < r` needs the revision never to decrease | `revGetterOk`: from a bound `RevLb n` the caller holds, `Rev()` returns `v ≥ n` (`runPre` gives `RevLb 0`) |
| `Compact` took `storeReader`, which asserts "never compacted" | `storeReaderC` |
| `Compact` dropped the compactor's permit | a permit `Pc r` travels with the proposal (the compactor's C1 permit; the gRPC caller's `True`) |
| `New` asked for contracts it never uses | moved to `Run`'s precondition (`runPre`); `New` and the constructors take none |
| `New`'s `10 ≤ ret` uncited for negative periods | the docstring cites the busy loop (`issues/etcd-compactor-periodic-tiny-retention.md`, etcd-io/etcd#22396) |
| the clock: what survives the trivial model, a phase-2 test | in its docstring |
| "possible Go issue": a negative retention busy-loops | false positive: already in `issues/` |
| `Compact` unprovable today (`dispatchOk` excludes compactions) | expected: the server side's model step (step 3) |

New failure patterns (the reviewer's and `LESSONS.md`): once-only resources spent per call; a resource
whose invariant contradicts the function; repairs introduce defects.

**Step 3 of phase 3 (planned): an easy and a hard proof.** The easy one, `Revision.Run` (the same
loop shape as `Periodic.Run`, with no window and no clock bound to chain); the hard one,
`Periodic.Run`. Each records its time and the spec problems it found that the reviews and the glue had
not; the comparison says whether the hard proof was needed (`notes/spec-first-plan.md`, "Phase 3").

**Review checkpoints** (`notes/spec-first-plan.md`, "Phase 1b", the feedback loop): at the freeze, a
retrospective of the revisions the review found against those the glue proofs found; at the end of
phase 4, every revision after the freeze attributed to a review criterion or to "none", and the
`spec-repair` `LESSONS.md` entries written from them. The first review (step 2b) ran on the phase-1b
tiers; its findings are scored on the added metrics afterwards.

**Next (step 3, the glue):** `New`, `newPeriodic`, `newRevision`, the getters; `EtcdServer.Compact`
over `processInternalRaftRequestOnce` (needs the compaction permit: `reqPropOk`'s compaction form,
`dispatchOk` and the KV model's compaction step); `NewServer`/`run` over the new `New.spec`
(item 3).

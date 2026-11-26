# Axiom review: the N3 clientv3 watch contracts across machines (`Watch_dist`, `RequestProgress_dist`)

Reviewed at branch `etcd-safe-n3/2026-11-25`, commit `641765e3dd` (worktree `eg-es-n3`, read-only, clean).
Evidence: a scratch Go module, kept in `notes/axiom-review/n3-watch-dist/` (`watch_test.go.txt`, renamed so no Go tool picks it up, with its `go.mod`/`go.sum`; its output in `output.txt`), run at
go1.27.3 against the pinned clientv3 fork (`upamanyus/etcd/client/v3@…df6af0c36a6b`) and grpc-go v1.84.0. The
servers are fakes: a gRPC `Watch` server whose answers the test scripts, an empty gRPC server, and a raw TCP
listener. There is no counterexample, so there is no branch, no Goose project and no Lean proof.

## Axioms

| # | Axiom | Files |
|---|---|---|
| 1 | `etcd_dist.Watch_dist.wp_proof` | `Proof/.../examples/etcd/dist/WatchDist.lean`; statement `Spec/.../dist/WatchDist.lean` |
| 2 | `etcd_dist.RequestProgress_dist.wp_proof` | the same files |

Shared precondition: `watchClientAt cl w eps V Γ` (`Proof/.../dist/WatchClientDist.lean`), which is
`isNewClient cl eps V ∗ clientNoProxy cl ∗ clientF cl "Watcher" ↦□ watcherIfaceOf w ∗ membersAt eps Γ`.
I also read, where they interact: `S2Interim.lean` (`etcdSvc`, `etcdAddrAt`, `membersAt`), `Serve_dist`,
`Client.Close.wp_proof`, grpc's `grpcServes`/`grpcServeTok` (`InvGrpcRun.lean`) and `ClientConn.NewStream`.
Earlier verdicts: `notes/axiom-review/n2-kv-dist.md` (the KV siblings, `Serve_dist`, `etcdSvc`: all sound after
re-review). `notes/audit.md` has no row for these two yet.

## Verdicts

| # | Verdict | Findings |
|---|---|---|
| 1 `Watch_dist` | **sound, with docstring corrections** | F1, F2, F3, F5 |
| 2 `RequestProgress_dist` | **sound, with a docstring correction** | F3 |
| (interaction) `Serve_dist` | its docstring must name the watch streams once these axioms are adopted | F4 |

No finding is a counterexample. F3 is the most important: it records what the `∀ V` form's soundness depends on.

**How the statements compare with the proved specs.** I compared the statements term by term with
`watcher.Watch.spec` and `watcher.RequestProgress.spec`.
- `Watch_dist` has the same three `isPkgInit`s, `watchCtx`, `outMD`, `optsAt`, the same pure premise
  (`isRangeWatchP`, `¬ opWatchPanics`, `1 ≤ rev`, `watchSizeOk`), and the same AU (masks, `kvRoom`, `□ Q σ`), at
  `Γ.kv` instead of `γ`.
- The post is the same SPSC channel, consumer and cursor. Its elements are `watchStateElemP Γ.kv … Q True`
  instead of `watchStateElemP V.kv … Q (auth row)`.
- The auth row's premise (`authPubLbM`, the bound `n`) is dropped, and so is its fact in the post.
- `RequestProgress_dist` differs from its proved spec only in `isClientWatcher V w ↦ watchClientAt`.

So, as in N2, a counterexample has to come from the cross-machine part:
- something answers the stream that is not a member meeting `v3rpc.watchSpec` at names `kvSame` to `Γ.kv`;
- or a cross-machine behaviour (a restart, another endpoint) that the single-process proof does not cover;
- or the dropped `isClientWatcher`, through the watcher's lock (D, F3).

## Attacks tried, and why each fails

### A. Who answers the stream

N2's attacks A1–A10 (`n2-kv-dist.md`) carry over unchanged:
- one table per address;
- relays and replays blocked by the connection-indexed opaque protocols;
- `addrUnset` is spent, so neither an HTTP server nor an in-process gRPC server can use the address;
- `clientNoProxy`;
- `kvCongr` covers every name the post reads (`st` for the AU; `rlog`, `cret`, `c0`, … for `cmpOkOf`).

What is new for streams:

1. **A fake gRPC server that registers a `Watch` stream handler at `a`.** `grpcServes Svc ics regs sregs`
   (`InvGrpcRun.lean:151`) requires `name ∉ sregs.map Prod.fst` for every name the table has. With the opaque
   `etcdSvc Γ mid`, no program can prove `etcdSvc Γ mid "/etcdserverpb.Watch/Watch" = none`. So no stream
   registration is possible, and the same holds for unary ones (N2 A4). Only the empty server can serve the
   table.
2. **The empty server.** Measured (T2): one response, `Err() = Unimplemented ("unknown service
   etcdserverpb.Watch")`, then the channel closes. That is the error arm.
3. **A raw listener** (accepts, writes nothing). Measured (T3): no response at all, and `Watch` returns a closed
   channel only when the caller's context ends (3 s, the test's timeout). There is no stream error (F2). The
   post allows this.
4. **A gRPC call that reaches the member with requests other than the watcher's.** On this line, the only
   cross-machine route a verified program has to a stream is these two axioms. `ClientConn.NewStream.spec`
   needs `isGrpcStreamsMd`, an in-process registration, so it cannot reach a set address. The requests are
   therefore the watcher's own (`toPB` creates under the in-process preconditions, cancels, progress
   requests).

### B. Mixing with the proved in-process watcher specs

To use `watcher.Watch.spec`, `Close.spec` or `closeStream` on the dist client, a program needs
`isClientWatcher V w`, which contains `watchConnFacts V`. That needs `isGrpcStreamsMd V.addrs …`, which is
`grpcAddrIs a γ` at each address (in-process). No set address has it, because `addrUnset` is spent. Using
another address list does not help: `grpcConn` is an opaque axiom (`InvGrpcBase.lean:1238`), and no law turns
`grpcConn conn eps` into `grpcConn conn V.addrs`. `isNewClient_watcher_of` needs the same `watchConnFacts`. So no
cross-machine program can call the proved specs on this watcher.

**Correction (2026-11-26, `wenv-isnewclient.md` F2).** "No cross-machine program can call the proved specs on
this watcher" is false. A program can `Listen` at an endpoint, `grpc.start` a server with the `Watch` handler
on that listener (giving `grpcAddrIs`, hence `watchConnFacts`), and set the address's protocols to `etcdSvc`'s
from `netAddrLeft` (`addr_set_proto_tok`, giving `etcdAddrAt`): it then holds both `isClientWatcher` and
`membersAt` for one watcher. The verdict stands for another reason: such an address is never served
(`grpcServes` of the opaque `etcdSvc` is unprovable with a stream registered, an address has one table, and
`etcdstart.Serve`'s `Listen` fails on the open listener), so the watcher's streams get no response
(`wenv-isnewclient.md` W1, W2).

### C. Resumption, lagging and restarted members, snapshots

- **The client's resume revision is the cursor plus one, and it moves only forward.**
  - `serveSubstream` (`watch.go:873-885`) uses the last event's revision plus one, or a progress revision plus
    one if that is larger.
  - Measured (T6): after events at revisions 2 and 3 and an `Unavailable`, the re-sent create starts at 4, on
    the same or the other endpoint (`creates [1 4] at [B A]`).
- **A lagging member, and a restarted member whose backend is behind what it sent before the crash:**
  - It is a prefix of the committed history, which is what the in-process proof already handles (W3b: several
    members, one cursor).
  - A watch from a revision the member has not reached is synced, and `newWatcherBatch` keeps only events with
    `ModRevision >= minRev`. So when the member re-applies revisions below the start, it sends none of them.
  - Its progress is sent only when `rev >= w.startRev` (`watchable_store.go:539`).
  - Every progress path goes through `progressIfSync`: the periodic one (`progress`) and `RequestProgressAll`
    (`progressAll`). Every other `send` carries events (lines 309, 401, 490).
  - Compaction responses are cancels with `CompactRevision ≠ 0`, which is the error arm.
- **A restart breaks the connection.** The new incarnation's streams are new streams with new ids. Nothing
  from the old incarnation arrives on them.
- **A member restored from a leader's snapshot** carries that backend's compaction. The compaction is a
  committed log entry, so `cmpOkOf` (`kvCmpPermit`) is the cluster's.
- **The member's configuration.** `memberUp` fixes `WatchProgressNotifyInterval = 0` (the default interval) and
  auth off. These are the configuration facts the in-process server proof is stated at.

### D. The `∀ V` form and the watcher's lock (F3)

- `isNewClient cl eps V` holds `sync.isMutex (watcher.mu) (watcherMu V' w callSl)`, where `V'` is `V` with the
  connection fields replaced.
- Each stream in the map carries `isWGS V' G`, which contains `watchSrvFacts V'`. That contains
  `watchConnFacts V'`, whose pure conjunct is `∃ i, i < V.nm ∧ …` (`InvWatch.lean:550`).
- So for `V.nm = 0`, `isWGS V' G ⊢ False`, and `watcherMu` with a non-empty map is `False`.
- `Watch` puts a stream into the map and unlocks (`watch.go:335-350`). So, at such a `V` and at today's
  definitions, `Watch_dist` is not a valid Iris triple: no proof could re-establish the lock invariant.
  `RequestProgress_dist` is the same (`watch.go:416-428`).
- For a general `V`, the invariant cannot be proved but is not refutable either.

Why this does not lead to a counterexample:
1. `mu` is an unexported field, so only `clientv3`'s code locks it.
2. Every spec of code that locks it falls into one of two groups:
   - it requires `isClientWatcher V w`, which no cross-machine program has (B): `watcher.Watch`,
     `RequestProgress`, `Close`, `closeStream`;
   - or it is an axiom whose post says nothing of the lock: `Watch_dist`, `RequestProgress_dist`, and
     `Client.Close.wp_proof` (pre `clientCoreAt`, post `True`). Its Go body calls `c.Watcher.Close()`,
     `client.go:147-159`, which locks `w.mu` and closes every stream.

So no proof can observe the broken invariant. Also, `Client.Close` with a cross-machine stream in the map does
not panic in Go (T5: the channel closes, `Close` returns). The docstring's own margin argument leaves
`Client.Close` out, and does not say that the argument is about encapsulation rather than truth (F3).

### E. `RequestProgress_dist`

- `watch.go:413-444`: with no stream for the key, it creates one (`run` dials and opens it). Measured (T7): one
  stream opened, `nil` returned.
- After `Close` it returns `errors.New("no stream found for context")` (T7). The other returns are `ctx.Err()`,
  the stream's `closeErr` (a raw grpc error or `v3rpc.Error` of one), or a recursive call. These are the
  in-process spec's cases, under the same grpc model.
- The server answers with `progressAll`, which needs every watcher of the stream synced and `rev >= startRev`.
  The client broadcasts the answer only to substreams already re-created (`broadcastResponse` over
  `w.substreams`, `watch.go:756-765`). So the progress arm holds per substream, as in one process.

### F. Error arms against the real behaviour

| Case | Go behaviour | Arm |
|---|---|---|
| halting stream error, watch context live | one response with `closeErr`, then close (`closeSubstream`, `watch.go:499`) | error |
| compaction | `Canceled` with `CompactRevision ≠ 0`, dispatched (`ErrCompacted`), then close | error |
| create refused (with a reason) | `addSubstream` sets `closeErr`, then error response, then close | error |
| server cancel without a reason or compaction | channel closes, no response (T1; `watch.go:625-639`) | — |
| the caller's context ends | channel closes, no response (T4) | — |
| `Client.Close` | channel closes, no response (T5) | — |

The post allows all of these, because the channel may close at any position (`fun _ => True`). The docstring
claims more than this (F1).

### G. Other

- **Request size.** An oversized create fails the stream on the client (grpc's `SendMsg` finishes the stream),
  and a halting error follows. This is the same grpc model as in one process. `watchSizeOk` is kept.
- **Writes.** The watch makes none, and the AU's commit is persistent (`□ Q σ`), so a repeated firing is
  harmless.
- **Cross-world** (the `crossWorld` check): none. The axioms are triples. `watchClientAt` contains points-to
  facts, but no entailment concludes a pure fact about an opaque function of a pointer.
- **Deriving `False`.**
  - The post's new resources are fresh existential ghost names (`γw`), and per-element facts that exist only
    for responses.
  - With an unserved `Γ` (an address set by `etcdAddr_set`, no member), the only outcomes are an error arm or
    no response.
  - With `eps = []`, `New`'s spec requires an endpoint. Even if it did not, there would be nobody to answer.
- **`Γ.auth`.** Every member that can serve `Γ` has auth off (`memberUp`'s `E.authOn = false`, and
  `Serve_dist`'s `Γ.auth = false`). So no create is refused, and the docstring's auth bullet is vacuous (F5).

## Findings and proposed fixes (none applied)

- **F1. `Watch_dist`'s docstring, "Errors, faults, cancellation".** The docstring says: "A stream error that
  halts (any other status, a canceled context, the server's cancel, a compaction past the start …) is a
  response with an error …, after which the channel closes." That is false for three of the cases.
  - A server cancel without a reason (`Canceled`, `CompactRevision = 0`) closes the channel with no response
    (`watch.go:625-639`; T1).
  - When the watch's own context has ended, the channel closes with no response, because `closeSubstream`
    sends the error only when `ws.initReq.ctx.Err() == nil` (`watch.go:499`; T4).
  - `Close` gives no response either (T5).
  - Also, besides `isHaltErr`, `run` halts on etcd's no-leader error, an `Unavailable` (`watch.go:678`; only
    with `WithRequireLeader` metadata).

  Proposed text: "A halting stream error (a status other than `Unavailable`/`Internal`, or etcd's no-leader
  error), a refused create, or a compaction past the cursor (`CompactRevision ≠ 0`) gives a response with an
  error (the error arm, position kept, its compaction revision `cmpOkOf Γ.kv`), unless the watch's context has
  ended. Then the channel closes. A server cancel without a reason, the end of the watch's context, and
  `Close` close the channel with no response." The statement is unaffected.
- **F2. `Watch_dist`'s docstring, "Who answers".** The docstring says that a raw listener gives "a stream error,
  so the error arm or a closed channel". In fact it gives no stream error. clientv3 dials with
  `WaitForReady(true)` (`options.go:29`), so stream creation waits for a transport that never becomes ready.
  The watch gets no response, and `Watch` returns a closed channel only when the caller's context ends (T3).

  Proposed text: "… (a raw listener: no response; `Watch` returns a closed channel when the caller's context
  ends. A gRPC server registering nothing: `Unimplemented`, the error arm, then close)."
- **F3. The margin, "the watcher's environment" (both axioms' docstrings, and plan §22.3).** The docstring says:
  "No proved spec opens the lock without `isClientWatcher V w` (… `Client.Close` is names-only), so nothing but
  these two axioms acts on the lock without those facts." Two corrections:
  1. `Client.Close.wp_proof`, an axiom, also acts on the lock: `Close` calls `c.Watcher.Close()`
     (`client.go:150`). Its docstring's argument ("`watcher.Close`, proved, keeps the watcher's invariant") is
     in-process, and does not cover streams these axioms put in the map. Measured: no panic (T5).
  2. Say what the argument is. At a `V` with `V.nm = 0`, `isWGS V' G ⊢ False`, so after a call the lock
     invariant cannot hold of the real heap. The axioms are valid at every `V` only once the
     watcher-environment refactor takes `watchSrvFacts` out of `isWGS`. Until then their use is sound by
     encapsulation (D), not because the triple is true.

  Proposed text for the margin: "At today's `watcherMu`, a stream these axioms add to the map has no provable
  `isWGS V G` (it is `False` at `V.nm = 0`), so the `∀ V` triples are not provable before the
  watcher-environment refactor. Their use is sound because nothing observes the lock's contents: `mu` is
  unexported, and every spec of code that locks it either takes `isClientWatcher V w`, whose `watchSrvFacts`
  no cross-machine program has (`watcher.Watch`, `RequestProgress`, `Close`, `closeStream`), or is an axiom
  whose post says nothing of the lock (`Watch_dist`, `RequestProgress_dist`, `Client.Close`). Any new spec or
  proof that locks the watcher from `isNewClient`/`isClientWatcherCore` without `watchSrvFacts` voids this
  argument, and must be reviewed together with these axioms."

  Record that last sentence in the audit rows too. The alternative fix is to do the refactor before adoption
  (§22.5, question 3), which removes the issue.
- **F4. `Serve_dist`'s docstring (interaction; change it when these axioms are adopted).** `Serve_dist`
  enumerates the calls that reach `a` as "the clientv3 contracts (`KV_Put_dist`, …)". It argues that every call
  reaching a handler is "a unary call of etcd's table", and that its no-panic claim "covers every connection a
  verified program can make to `a`: the client contracts' calls and raw writes".
  - With these axioms, a verified program also opens `Watch` streams to `a`. They run the member's v3rpc watch
    handler, which is a stream handler and not a table entry.
  - The claim is still true. The streams carry only the watcher's create, cancel and progress requests, under
    `watcher.Watch.spec`'s preconditions (A4). The in-process proof of the member's watch handler covers those
    (`v3rpc.watchSpec` under `watchUp`; `memberUp`'s `srvWatchBuilt`).

  Proposed addition to `Serve_dist`'s docstring: "… and the watch streams of `Watch_dist`/`RequestProgress_dist`
  (the clientv3 watcher's create, cancel and progress requests, under `watcher.Watch.spec`'s preconditions),
  which the member's watch handler meets as in its in-process proof (`watchUp`)." Make this change in the same
  commit that adopts the axioms.
- **F5. Smaller docstring corrections.**
  - In the Spec docstring, "resumed from the cursor" should be "from the cursor plus one" (T6).
  - In the Proof docstring, the "Any auth mode" bullet is true of Go (a refused create is a canceled response
    with a reason, which is the error arm), but vacuous. Proposed: "every member serving `Γ` has auth off
    (`memberUp`, `Serve_dist`'s `Γ.auth = false`), so no create is refused; the statement does not constrain
    `Γ.auth`, and with `Γ.auth = true` no member serves `Γ`."
- **Retirement note (no change now).** "The statements do not change" holds only up to hypotheses. The retiring
  proof needs what `watchConnFacts_of_members` takes:
  - `context.ErrAny.spec`;
  - `errors.AsTarget EtcdError.ty`;
  - the `errors`/`fmt`/`rpctypes` `Assumptions` instances (the top level already carries these);
  - each member's `watchMemberFacts`, from the table entry.

  Like N2's note, these have to come from the entries or the top level, not from `watchClientAt`.

## Not tried

- **The in-process proofs themselves.** They are proved: `watcher.Watch`, the v3rpc watch handler, and the
  mvcc store under several members. The axioms inherit their correctness.
- **A real cluster across processes.** The tests use fake servers for the client's behaviour. The server-side
  claims (`progressIfSync`'s `rev >= startRev`, `newWatcherBatch`'s `minRev` filter, the compaction response)
  are argued from the pinned source and were not run.
- **A Lean counterexample.** There was no gap to build one on.
- **Crash durability.** That belongs to the crash proofs' trust.
- **Hostile gRPC clients that are not clientv3.** No verified program can make one across machines (A4).

## Re-review (commit `c9ad333c08`, 2026-11-25)

I checked the diff `641765e3dd..c9ad333c08`. It touches two files: `Proof/.../dist/WatchDist.lean` (docstrings
only) and `Spec/.../dist/WatchDist.lean` (one docstring line). **No statement changed**: both `abbrev`s and both
`axiom` lines are byte-identical, and so is `watchClientAt`.

- **F1 is closed.** The new "Errors, faults, cancellation" bullet matches the code and the tests:
  - these give an error response when the watch's context is live, then the close: a halting status (anything
    but `Unavailable`/`Internal`), etcd's no-leader error, a refused create, a compaction (`watch.go:499`,
    `:678`);
  - these close the channel with no response: a server cancel without a reason, the end of the watch's context,
    `Close` (T1, T4, T5; `watch.go:625-639`).
  - One precision, optional: `w.closeErr` is per gRPC stream, and a refused create sets it (`addSubstream`). So
    on a stream that has had a refused create, a later substream may get that stale error response before its
    close, for example on a server cancel. That is still the error arm, and with auth off (every member serving
    `Γ`) no create is refused. The text needs no change.
- **F2 is closed.** "A raw listener writes nothing, so (clientv3 dials with `WaitForReady`) no response comes and
  `Watch` returns a closed channel when the caller's context ends; a gRPC server registering nothing gets every
  stream `Unimplemented`, the error arm, then the close." This is what T3 and T2 measured.
- **F3 is closed.** The header's "The `∀ V` form" says three things, and all three are correct:
  - the triples cannot be proved at today's `watcherMu` and are not valid at `V.nm = 0` (that is the
    `watchConnFacts` pure conjunct, `InvWatch.lean:550`);
  - they are sound by encapsulation, with the same list of lock-taking code as section D, including
    `Client.Close.wp_proof` through `c.Watcher.Close()`;
  - the bolded rule for future specs that lock the watcher.

  Both axioms' docstrings now point to the header. `RequestProgress_dist`'s note ("a stream it starts") is
  right: it adds a stream only when the key has none.
- **F5 is closed.** The Spec docstring now says "resumed from the cursor plus one" (T6). The auth bullet now
  says that every member serving `Γ` runs auth off and that `Γ.auth` is unconstrained, and keeps the true Go
  remark about a refused create.
- **The retirement note is applied** to the header's "What retires them", as proposed.
- **Nothing false was introduced.** I checked each new sentence against the pinned `watch.go`, `client.go` and
  `options.go`, and against the tests' output.

**F4 (`Serve_dist`'s docstring): deferring it is acceptable, with a condition.**
- The finding is about how complete `Serve_dist`'s docstring is. Its statement and its no-panic claim stay true
  under watch streams (section A4 and F4), so nothing is unsound in the meantime.
- No exported result depends on `Watch_dist` or `RequestProgress_dist` yet: they are not in
  `etc/tcb-baseline.txt` and nothing imports `WatchDist.lean`. So no result rests on the two docstrings
  disagreeing.
- The condition: the commit where a workload first reaches these axioms (the first result whose
  `etc/tcb-report.py` roots include them) must carry F4's text in `Serve_dist`'s docstring. Track this in
  plan §22.7 and in the two audit rows. If that commit would land without it, F4 reopens.

**Final verdicts.**

| Axiom | Verdict |
|---|---|
| `etcd_dist.Watch_dist.wp_proof` | sound (F1, F2, F3, F5 applied) |
| `etcd_dist.RequestProgress_dist.wp_proof` | sound (F3 applied) |
| `Serve_dist`, docstring | F4 deferred to the first commit that reaches these axioms (accepted, tracked) |

Open: F4 only, deferred. The F3 rule stands as a standing review trigger for future specs: record it in both
audit rows.

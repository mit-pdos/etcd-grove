# The `axiom-tok` gate on the full `etcd_safe_nocrash` line (2026-11-26)

This note records the reasoning behind `etc/axiom-tok-allow.txt`'s entries for the axioms that `etcd_safe_nocrash`
reaches for the first time. It is a trace, not an `axiom`-skill review. The line is `etcd-safe-full/2026-11-26` @
`cb5da68ee3` (notes/etcd-dist-plan.md §30), and the entries are on `etcd-safe-full-atok/2026-11-26`. The commit
changes the allow file and this note only, so no axiom, statement or proof changes.

## What was run

Each tree was a fresh worktree with no `.lake`. Every run was on the VM.

- **Steps for each tree.** A full `vmlake build`, then `vmlake env python3 etc/tcb-report.py --check` (no `TCB_CACHE`),
  then `etc/axiom-tok-check.py --check --raw`, then `--selftest --reuse-raw`.
- **The comparison walk.** The gate's own `etc/AxiomTokCheck.lean`, at the default depth and the gate's `--part`
  flags, walked the new axioms beside their proved in-process siblings in one run. The siblings are
  `client.v3.kv.wp_Compact`, `kv.wp_Put`, `watcher.wp_Watch`, `watcher.wp_RequestProgress`, `lessor.wp_Grant`,
  `lessor.wp_Leases` and `lessor.wp_TimeToLive`. The run also included `wp_NewServer`, `server_new_auth_on` and
  `etcdstart.Serve.wp_proof`. The imported modules were `dist.TopLevelRobustness`, `client.v3.Link`,
  `etcdserver.Results` and `etcdstart.Serve`.
- **The instrumented walk.** An untracked copy of the checker, not kept, pushes an unfold stack in both `walkI` and
  `walkProp`. It prints one line per token, per atom use, per `∃` binder and per naked use. It was run on
  `Watch_dist`, `RequestProgress_dist`, `KV_Compact_dist`, `Lease_Grant_dist` and `watcher.wp_Watch`.

Raw outputs are not kept in the repository. They are in the job scratch directory: `atok-line.jsonl`,
`atok-lean.jsonl`, `cmp1.jsonl` and `instr1.err`.

## Plain lean `93687cba82`: green

| check | result |
|---|---|
| `tcb-report --check` | ok |
| `axiom-tok --check` | ok, 357 Prop axioms walked: 319 pass, 38 by an entry or pair |
| `axiom-tok --selftest` | 0 failures |

No finding of the line is lean's.

## The line at `cb5da68ee3`, before these entries

- **The gate failed** with 47 axioms needing an entry, 2 unknown from the scenario cap and 9 unknown from truncation.
  The selftest failed on `real-pass EtcdServer.leaseTimeToLive.wp_proof` (a rule-5 taint).
- **Nine roots.** Only nine axioms have findings of their own that no entry covers. All nine are new on the line, and
  all are rule 2 and rule 7. Their uncovered rule-2 findings taint `grpcConn`, `credsYieldRaw` and
  `metadata.builtRawMDRaw` (rule 5).
- **The taint spreads.** It reaches 20 opaque predicates, which puts every axiom producing one of them into the
  report.
- **The other 40 are only cascade.** Each has only rule-5 findings left. That holds for the 38 reported as "need an
  entry" and for the two capped walks, `NewServer_dist` and `Serve_dist`.
- **No existing entry needs a re-key.** Every existing entry's keys are exactly its walk's keys on the line. This
  includes M1's KV/Serve/NewServer/PeerServe/bootstrap entries and the grpc/etcdserver ones. On both trees, with each
  tree's own allow file, `NewServer_dist`, `Serve_dist` and `PeerServe_dist` have no walk key outside their entry and
  no entry key outside their walk. No stale entry or `trunc` line was reported.
- **After the entries.** With the nine entries and their nine `trunc` lines, the same raw output judges green: 366
  Prop axioms walked, 319 pass and 47 by an entry. No predicate is tainted.

## Classes

| class | axioms | key |
|---|---|---|
| (a) re-key | none | (none: every existing entry already matches its walk) |
| (b) a reviewed sibling's key | `KV_Compact_dist`; F2's `Lease_Grant_dist`, `Lease_GrantLive_dist`, `Lease_LeasesGranted_dist`, `Lease_LeasesLive_dist`, `Client_LeaseLeases_dist`, `Client_LeaseTimeToLive_dist` (7) | `2:L:0:handedtoacallback8/supplieddirectly1,7:P:IPropGF`, exactly `KV_Put_dist`'s accepted entry |
| (c) hand-traced | `Watch_dist`, `RequestProgress_dist` (2) | `2:L:0:handedtoacallback8/supplieddirectly0,7:P:IPropGF` |
| rule-5 cascade (no entry) | the 40 above, cleared by the nine entries | none |

Every one of the nine walks has 8 scenarios. None is capped, none is a mint candidate, and none has a rule-3
finding.

### (b) The seven with `8/1`

**The tokens.** The instrumented stacks are `KV_Put_dist`'s exactly:

- The pre's `levelTok 0` is consumed (`cb=0 flips=1 stack=[spec]`), and the post's is produced (`cb=0 flips=2`).
- Sixteen token occurrences come in 8 pairs, each pair `pol=pos cb=3 flips=2` then `pol=neg cb=3 flips=3`, with the
  stacks `[etcdInterceptorOk | etcdInterceptorOkM>etcdInterceptorOkW, isEtcdConn, X, isNewClient, kvClientAt |
  leaseClientAt, spec]`.
- `X` ranges over `clientKVAt`, `kvObjAt`, `lessorAt>lessorRemoteAt` and `authObjAt`: the four connections that
  `isNewClient` holds, with two contracts each. Each contract's post returns the token its pre took.

**Why it is not a mint.**

- **Plain rule 2 passes:** 9 tokens produced against 9 consumed.
- **Go.** `kv.Compact` calls `kv.remote.Compact`, which is `retryKVClient.Compact`. `lessor.Grant`, `Leases` and
  `TimeToLive` call `l.remote.LeaseGrant`, `LeaseLeases` and `LeaseTimeToLive`, which are `retryLeaseClient`'s with
  `withRepeatablePolicy`. Each goes through the stub's `Invoke` to grpc's unary interceptor, called on the caller's
  goroutine, which returns before the function does.
- **So the caller's one token is lent to one call at a time and given back.** That is the reading of
  `KV_Put_dist`'s entry.
- **The proved in-process siblings show the same pattern.** `kv.wp_Compact`, `lessor.wp_Grant`, `wp_Leases` and
  `wp_TimeToLive` were walked in the same run. Each has `2:L:0:handedtoacallback2/supplieddirectly1`, because its
  pre names one connection where `isNewClient` names four.

**Rule 7, `∃ P : IProp`.** It is naked in `isCancelCtxOf`, under `ctxOk` in those contracts' pres: the
`*cancelCtx` Done proposition of the context the axiom hands the interceptor, as in `KV_Put_dist`'s entry.

**The six lease axioms are F2's** (etcd-grove-03), and are marked for etcd-grove-03's confirmation.
`f7-auth-axiom-tok.md` ("Rule 2, 8/1") read the same key the same way for the auth-on `Lease_*On` variants. Those
variants are not reached on this line.

### (c) `Watch_dist`, `RequestProgress_dist` with `8/0`

**The tokens.** The walk has the same 8 contract pairs, with the same stacks under `watchClientAt > isNewClient`.
There is no token at `cb=0`: neither the pre nor the post has one, and neither has the source spec.

**What rule 2 says.**

- Plain rule 2 passes: 8 tokens produced against 8 consumed.
- 2b fails, because no token is supplied directly.

**Why the axiom does not mint the 8 tokens.** They are never a token the caller gives or receives:

- **Go, and the translation** (`Code/.../client/v3`, `watcher.Watch.impl`, `RequestProgress.impl` and
  `newWatcherGRPCStream.impl`). `Watch` and `RequestProgress` take the watcher's lock and find or create the
  stream. Creating it is `newWatcherGRPCStream`, whose `go wgs.run()` is the translation's `Fork`. Then they
  exchange messages over `reqc`/`retc`/`donec`. Neither makes an RPC on the caller's goroutine.
- **Only the forked `run` uses the connection.** It opens the gRPC stream through `openWatchClient`, which calls
  `w.remote.Watch` (a stream, so through the stream interceptor). The unary contracts the walk counts
  (`etcdInterceptorOk`/`etcdInterceptorOkW`) are never called by either function.
- **The token `run` has is its own.** The proved `watcher.newWatcherGRPCStream` (`watcher__newWatcherGRPCStream.lean`,
  `wp_fork_tok_body`) gives `run` the fresh thread token of its `go`. `watchGRPCStream.run.spec` takes that
  `threadTok` and returns it, and `run`'s proof splits it into `levelTok 0` around each call (`threadTok_level0`). The
  counted contracts are never called; the only connection call, `run`'s stream open, uses the forked goroutine's own
  token, from the fork rule, and the caller neither gives nor receives it. That fork-token flow is the proved
  in-process code's: the dist call runs the same translated code, and no proof covers it (the independent triage,
  [watch-dist-axiom-tok-triage](watch-dist-axiom-tok-triage.md)).
- **The proved in-process siblings pass with no finding.** `watcher.wp_Watch` has 3 scenarios and
  `wp_RequestProgress` has 2. The instrumented walk of `wp_Watch` meets no token: `isClientWatcher` exposes no
  contract with a token.
- **The difference is `isNewClient`.** The dist pre `watchClientAt` adds it, and its four connections' unary
  contracts (the client's other fields) are visible to the walk.

The entry rests on this trace, not on a sibling's key, so it is marked for an independent triage.

**Rule 7.** `P` is as in (b): the contracts' `ctxOk`.

## Truncations

All nine walks have the same 27 truncation notes. Those 27 are exactly the notes of `KV_Put_dist`'s, `KV_Get_dist`'s
and `Txn_Commit_dist`'s walks, which are already on the ratchet:

- `isNewClient`'s contexts: `isCancelCtxOf`, `isCancelCtx`, `isClosedchanInit`, `isMutex` and `named` past
  `--depth`, and `stuck projection: cd.4`;
- the models' projections: `Req.toProtoMsg.5 inp m`, `Rep.toProtoMsg.*`;
- `status.statusAt*`, `errorMsgIs`, `grpcStatusIs`, `isChan`;
- `stuck: dghostVar`.

None of the notes is in a post. Each axiom gets a `trunc` line.

## Gates on `etcd-safe-full-atok/2026-11-26`

These results were taken on the VM at `e655019199`, the entries' commit.

| check | result |
|---|---|
| `tcb-report --check` | trust base matches `etc/tcb-baseline.txt`: 383 axioms, 0 `sorry` (unchanged) |
| `axiom-tok --check` (a fresh Lean run) | ok, 366 Prop axioms walked: 319 pass, 47 by an entry or pair |
| `axiom-tok --selftest --reuse-raw` | 0 failures; `real-pass EtcdServer.leaseTimeToLive.wp_proof` is ok again |

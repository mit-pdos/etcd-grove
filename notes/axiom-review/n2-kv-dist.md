# Axiom review: the N2 clientv3 contracts across machines, `Serve_dist` and `etcdSvc`

Reviewed at branch `etcd-safe-n2/2026-11-25`, commit `5d4f0a7151` (worktree `eg-es-n2`, read-only; it had one uncommitted
edit by someone else, to `KVClientDist.lean`, which adds `putGetInvK` and touches none of the reviewed statements).
Evidence branch: `axiom/n2-kv-dist` in the worktree `n2-scratch/review-wt`, package `examples/axiomcx/n2kvdist/`
(a Go test only; no counterexample, so no Goose project and no Lean proof).

## Axioms

| # | Axiom | Files |
|---|---|---|
| 1 | `etcd_dist.etcdSvc` (the opaque table), with `etcdAddrAt`, `membersAt`, `DistView`, `etcdAddr_set` (theorem) | `Proof/.../examples/etcd/dist/S2Interim.lean` |
| 2 | `etcd_dist.Serve_dist.wp_proof` | `{Spec,Proof}/.../dist/ServeDist.lean` |
| 3 | `etcd_dist.KV_Put_dist.wp_proof` | `.../dist/KVPutDist.lean` |
| 4 | `etcd_dist.KV_Get_dist.wp_proof` | `.../dist/KVGetDist.lean` |
| 5 | `etcd_dist.KV_Delete_dist.wp_proof` | `.../dist/KVDeleteDist.lean` |
| 6 | `etcd_dist.KV_Compact_dist.wp_proof` | `.../dist/KVCompactDist.lean` |
| 7 | `etcd_dist.Txn_Commit_dist.wp_proof` | `.../dist/TxnCommitDist.lean` |

The shared client precondition is `kvClientAt` (`KVClientDist.lean`).

## Verdicts

| # | Verdict | Findings (all docstring or premise level, none a counterexample) |
|---|---|---|
| 1 `etcdSvc` | **sound** (consistent; no law) | none |
| 2 `Serve_dist` | **sound**, docstring corrections | F2 (`Γ.auth` premise), F4 (stale HTTP route; "every byte" overclaim) |
| 3 `KV_Put_dist` | **sound** | F5 (who answers: also an empty server or a raw listener) |
| 4 `KV_Get_dist` | **sound**, docstring correction | F3 (retry cases) |
| 5 `KV_Delete_dist` | **sound** | F5 |
| 6 `KV_Compact_dist` | **sound**, docstring correction | F1b (Compact's retry, "the update") |
| 7 `Txn_Commit_dist` | **sound**, docstring correction | F1a (a read-only Txn is not retried as a range) |

General point. Each client contract is, word for word, the proved in-process spec (`kv.Put.spec` at `dup = false`,
`kv.Get.spec`, `kv.Delete.spec` at `dup = false`, `kv.Compact.spec`, `txn.Commit.spec` at `dup = false`) with
`isKv api Γ.kv dup` replaced by `kvClientAt cl api eps V Γ` and `kvErr` dropped from the error arm. I compared all five
statements with their in-process specs and found no other difference (Txn's `□?dup` at `dup = false`, Get's `□`, the
posts and the masks are identical). So a counterexample has to come from the cross-machine part: some reply reaching
the client that is not the reply of a member whose handlers meet the in-process handler specs at names `kvSame` to
`Γ.kv`, or a write that is delivered twice, or a premise of `isKvOf` that the dist setting drops. I attacked those
three things and found nothing.

## Attacks tried, and why each fails

### A. A reply from someone other than a `Serve_dist` member of `Γ`

1. **Two tables at one address, or two views for one address.** `etcdAddrAt a Γ mid` is
   `∃ σ, grpcAddrAt a (etcdSvc Γ mid)`, which is `addrProto a (grpcCliPI Svc) (grpcSrvPI Svc) ∗ depSlotsCtx`.
   `addrProto` is an invariant at `addrN a` that holds `netPend NG a S`, and only one such invariant can be allocated,
   because `addrUnset a`'s `netPend NG a ∅` is exclusive. That holds under every `NetProtoGS π`, since `netPend` is the
   extension's own state and not `π`'s. So `a` gets one table, once. A fresh `π'` from `netProto_alloc` does not
   help: it cannot get a second `addrProto a` either.
2. **A raw listener or acceptor at `a`.** `listen_au` lets the holder of `addrProto` listen. But writing needs
   `protoPrefix (grpcSrvPI Svc) cn W`, and `grpcSrvPI` is a Lean `opaque` (it cannot be unfolded) with no law. So the
   only write it can make is the empty one, and the client sees a silent peer and gets a deadline error, which is the
   error arm.
3. **A relay** (accept at `a`, dial `b`, forward the bytes). The protocols take the connection number `cn`. A byte
   string read on `cn₁` gives a fact about `grpcCliPI Svc cn₁`, while writing on `cn₂` needs
   `grpcCliPI Svc' cn₂`. These differ even when `Svc' = Svc` (relaying between two addresses of one view), and
   nothing relates them. Replaying a reply onto another connection is blocked the same way. `bridge.New` needs
   `netAddrLeft` of its listening address, which neither `etcdAddr_set` nor `listen_au` leaves.
4. **A gRPC server with fake KV handlers at `a`** (`Server.Serve`). `grpcServeTok gs lis a Svc` requires
   `grpcAddrAt a Svc`, so `Svc` must be `etcdSvc Γ mid` (by 1). It also requires `grpcServes Svc …`: every
   registered name in the table must meet that entry, and every table name must stay out of `sregs`. With an opaque
   table, neither can be proved for any nonempty registration list, so only the empty server serves it. In grpc-go
   v1.84 an unknown method gets `Unimplemented` without running the unary interceptors (`handleStream`). No
   `UnknownServiceHandler` option has a spec (`Spec/google_golang_org/grpc/` lists none). `Unimplemented` is not
   retried, so the client takes the error arm.
5. **A single-process program, which also has `addrClaim a`** (`goose_adequacy_start`'s `startRights`). It can call
   `etcdAddr_set`, then `listen_au` to get `netListenerOpen l a`, add `addrClaim a` to get `netListenerAt l a`, and
   then `grpc.start` with its own handlers. But `Server.Serve` still needs `grpcServeTok` and so
   `grpcServes (etcdSvc Γ mid)` (4). The in-process `Serve` and `http.reserve` need `netAddrFree a` (the same
   `addrUnset`), and `bridge.New` needs `netAddrLeft a`. Blocked. The dist starts (`etcdClusterStart`) hand out no
   `addrClaim` anyway.
6. **An HTTP server at `a`** (Serve_dist's docstring lists this route). `http.register` needs `httpProtoOwn a P`.
   That comes from `reserve`, which needs `httpAddrNet a`, which comes from `httpAddrFree_set` over `netAddrFree a`,
   whose `addrUnset` `etcdAddr_set` has already spent. So the route is impossible, not merely harmless (F4).
7. **A proxy.** `kvClientAt` includes `clientNoProxy` (review F1). The endpoints are literals (`AddrOk`).
8. **Another cluster's member, or a member whose KV names differ.** `Serve_dist` requires `kvCongr ρ.rd.kv Γ.kv`,
   which covers every field the contracts read: `etcdKV` reads `st`; `kvRevLb`/`kvRevLbZ` read `rlog` and the model's
   `c0`, `ch0`, `log0`; and `cmp`, `cret`. `kvCongr` implies `kvSame`, which is what `isKv_intro` asks of a member.
   Names `kvCongr` to `Γ.kv` come only from the cluster's own slice (`wp_StartServer1_slice`: `memberSliceOf` is
   exclusive) or from a restart of its member (`restartNames`). A second cluster has fresh `st`/`rlog`. Two `kvInv`s
   over one `st` cannot both be allocated: each holds a half of the ghost variable, and the client's `etcdKV` holds
   the other half. A duplicate member inside a cluster is `NewServer_dist`'s concern, reviewed in §17.3.
9. **One member serving two views.** `memberUp` is consumed by `Serve_dist`, so a member serves once. Two views
   `kvCongr` to one member's names agree on every field the contracts read (8), so nothing changes.
10. **Cross-world facts** (the `crossWorld` check). There are none. `etcdSvc` is a constant of `Γ, mid` with no
    heap, and no entailment has a pure conclusion about an opaque function of a pointer.

### B. A write applied twice (the one-shot update fires twice)

The pinned fork's `retry_interceptor.go` and `retry.go` give these paths:

- `Put`, `DeleteRange`, `Txn` and `Compact` have no retry policy (`retryKVClient`, `retry.go:114-128`), so they are
  `nonRepeatable` (`defaultOptions`).
- A `nonRepeatable` call is retried only on these errors:
  - an Unavailable error with the old balancer's two descriptions. grpc v1.84 has neither string.
  - the learner refusal with more than one endpoint (`isSafeRetry`).
  - a token refresh (`shouldRefreshToken`): an auth refusal.
- A per-attempt context error with the caller's context still live returns at once for `nonRepeatable` (this is the
  fork's fix, lines 80-91).

All three retried cases are refusals that the server makes before it proposes. `memberUp` gives `E.authOn = false`.
The voter fact is the one `etcd_noRefusal` already assumes. grpc-go's transparent retry resends only a stream the
server never processed: `REFUSED_STREAM`, or a `GOAWAY` past the stream (its `maxStreamID`). No client resends a
proposed write.

Measured (`examples/axiomcx/n2kvdist/retry_test.go`, go1.27.3, the pinned clientv3/grpc, the client of
`etcdstart.NewClients`, a counting gRPC KV server). Seven calls were made: Put, Get, a serializable Get, Delete,
Compact, a read-only Txn and a writing Txn. The table gives the attempts the server saw.

| Server's answer | Put | Range (2 calls) | DeleteRange | Compact | Txn (2 calls) |
|---|---|---|---|---|---|
| `ErrGRPCTimeout` (Unavailable, "request timed out") | 1 | 154 | 1 | 1 | 2 |
| `DeadlineExceeded` status, caller's context live | 1 | 156 | 1 | 1 | 2 |
| learner refusal, 2 endpoints | 100 | 200 | 100 | 100 | 200 |

The last row is the refusal path that the members exclude. It confirms why the contracts depend on members that never
refuse.

### C. Premises of `isKvOf` that `kvClientAt` drops

`kvClientAt` keeps `isNewClient`, `clientNoProxy` and the `KV` field. It replaces `kvRegs ms`, `srvStart`, `kvSame`,
`noRefusalAt` and `receiptBound GF ≤ 2^62` with `membersAt eps Γ`. Each dropped fact is supplied wherever a success
can occur, because a success needs a `Serve_dist` member (A):

- `kvSame` comes from `kvCongr`.
- `srvStart` (`committedAtLeast _ 0`, `kvLogLb _ []`) comes from the member's start.
- `noRefusalAt` comes from `memberUp`'s auth off and the voter fact.
- The receipt bound comes from `Serve_dist`'s `[ReceiptBoundLe GF (2^48)]`.

An endpoint that is set but never served answers nothing, so the call ends in the error arm.

### D. The success and error arms against real behaviour

- **Error arm, `err ≠ nil ∧ resp = null`.** `kv.Put`/`Get`/`Delete` return `r.put`/`r.get`/`r.del` of a zero
  `OpResponse` on error. `Compact` and `Commit` return `nil, err`. `ContextError` keeps a non-nil error non-nil.
- **Header revisions.** Put: `σ.rev + 1`. Delete: unchanged when nothing is deleted. Read-only Txn: `σ.rev`; writing
  Txn: the commit's. Range: the current revision. These are as in-process, and the handlers are translated.
- **prevKV, count, selection.** As in-process.
- **Serializable reads.** The claim is about some `σ`. A lagging or restarted member's state is a model prefix state,
  and a read past it is `ErrFutureRev` (error arm).
- **Compaction errors.** `ErrCompacted` and `ErrFutureRev` are errors. Compaction is a log entry of the model
  (`cmpLogOk`), so later `σ.at` reads see it.

### E. `auth = false` and `cmp = true`

- `cmp` is tied: `kvCongr` forces the member's `cmp`/`cret` to be `Γ.kv`'s, so `Γ.kv.cmp = true` holds only of a
  compaction-mode cluster.
- `Γ.auth` is not tied to anything (F2). `Serve_dist` serves `etcdSvc Γ mid` for every `Γ.auth`. But every member it
  serves has auth off (`memberUp`: `E.authOn = false`; `kvInv`: `γ.raft.authOn = false`, so no `AuthEnable` is ever
  applied). The premise `Γ.auth = false` in the write contracts therefore restricts their use and nothing else. What
  actually makes a write at-most-once is `memberUp`. There is no attack: no auth-on member can serve the table, and
  no verified program can enable auth across machines (there are no Auth contracts).

### F. Deriving `False` from the contracts, or with the in-process specs

- A success needs an AU over `etcdKV Γ.kv` (a ghost-variable half), or for Compact a `kvRevLbZ`, which only a write's
  reply gives.
- An unserved `Γ` gives only error arms.
- A lease-granting cluster's `kvInv` owns the whole variable, so no AU can be built there.
- `etcdSvc` is data: `GrpcSvc` is inhabited by `fun _ => none`.

None of these combinations gives `False`.

### Not tried

- The in-process handler and client proofs themselves (proved; their trust-boundary grpc axioms were reviewed
  separately).
- Crash-restart durability (the crash proofs).
- `apply.backendUnderQuota` and the other top-level premises (they are known trust).
- Resource exhaustion through many raw connections (no panic in Go; the thread bound is the model's).

## Findings and proposed fixes (none applied)

- **F1a, `Txn_Commit_dist`'s docstring.** It says "a read-only transaction is retried as a range (its update
  persistent)". That is false. `(*txn).Commit` sends with `txn.callOpts = kv.callOpts`, and `retryKVClient.Txn` adds
  no policy, so every Txn is `nonRepeatable`. `isWrite` is computed in `Then`/`Else` and never read. The test
  measured one attempt per Txn after Unavailable. Proposed text: "every transaction is retried only after a refusal,
  which an auth-off voter never sends; the read-only cases' update is persistent anyway." The statement is
  unaffected.
- **F1b, `KV_Compact_dist`'s docstring.** It says "A compaction past the compacted revision is an error, so a retry is
  harmless either way". Compact is `nonRepeatable` too (measured: 1 attempt), so it is retried only after a refusal.
  A repeated compaction at the same revision is `ErrCompacted`, which is the error arm. Also drop "the state the
  update fired at": Compact takes no update.
- **F2, `Serve_dist`: add the pure premise `Γ.auth = false`** (or `Γ.auth = E.authOn`, which is `false` by
  `memberUp`). The start's view has `auth := false` (`ClusterNames.view = DistView.ofKV`), so putget's `Member` proof
  discharges it with `rfl`. With it, the table at `Γ` is served only by members in `Γ`'s auth mode, and the write
  contracts' `Γ.auth = false` premise means what their docstrings say. S2 needs this too: when `etcdSvc Γ` is defined
  with auth-on entries for `Γ.auth = true`, an auth-off member would not obviously meet them. Until then, say in the
  write contracts' docstrings that `memberUp`'s `E.authOn = false` and `etcd_noRefusal`'s voter assumption are what
  make a write at-most-once, and that `Γ.auth = false` restricts their use.
- **F3, `KV_Get_dist`'s docstring.** It says a range is retried "on `Unavailable`". It is also retried after a
  per-attempt context error while the caller's context is live (`isContextError`, `repeatable`: `continue`), after
  the learner refusal (two or more endpoints), and after an auth token refresh. All are harmless because the update
  is `□`. The docstring should list them, or say "any number of times".
- **F4, `Serve_dist`'s docstring.**
  1. Delete "(through `listen_au` and `http.register`) an HTTP server": `register` needs `reserve`, which needs
     `httpAddrNet a`, which needs the spent `addrUnset a` (A6).
  2. The sentence "covers every byte arriving at `a`, from any client (an HTTP `RoundTrip`, a raw dial)" claims more
     of etcd and grpc-go than the axiom needs, and more than was checked: a hostile gRPC client's well-formed request
     could reach handler paths the in-process proof covers only under the client specs' preconditions. Under the
     opaque protocols, the only bytes a verified program can send to `a` are grpc's transport's calls through the
     five client contracts (under their in-process preconditions) and the empty write of a raw dialer. Proposed text:
     "covers every connection a verified program can make to `a`: the client contracts' calls, and raw connections
     that write nothing".
- **F5, the five client contracts' "who answers" bullet.** It says "served only by `Serve_dist`". Add "or by an
  empty gRPC server (every call `Unimplemented`) or a raw listener (writes nothing): both give the error arm", as
  `Serve_dist`'s docstring already does.
- **Retirement note (no change now).** S2's proof of the client contracts must take the receipt bound and `srvStart`
  from the table's entries or the members, since `kvClientAt` no longer carries them (C).

A forward warning. The deployment plan's auth workload runs `AuthEnable` across machines (§18's workload table). Once
Auth contracts across machines exist, `Γ.auth` has to be the cluster's real mode. F2's premise is the hook for that.

## Re-review (commit `48632ff055`, 2026-11-25)

I checked the diff `5d4f0a7151..48632ff055` of `Spec/.../dist/ServeDist.lean` and `Proof/.../dist/{ServeDist,KVPutDist,KVGetDist,KVDeleteDist,KVCompactDist,TxnCommitDist,KVClientDist}.lean`.

- **F2 is closed.** `Serve_dist.spec`'s pure premise is now `… ∧ kvCongr ρ.rd.kv Γ.kv ∧ Γ.auth = false`.
  - The change only weakens the axiom: one more premise, the same post.
  - Its one caller, putget's `Member`, discharges it by `rfl` at `c.view`.
  - The table at `Γ` is now served only by members in `Γ`'s auth mode, so the write contracts' `Γ.auth = false` means what their docstrings say.
- **F1a is closed.** The Txn docstring now says every transaction is sent non-repeatable (`Commit` sends with `kv.callOpts` and never reads `isWrite`). That matches the code and the measurement.
- **F1b is closed.** The Compact docstring now says it is non-repeatable and retried only after a refusal, and that a success claims nothing of the state.
- **F3 is closed.** Get's retry cases now include the per-attempt context error, the learner refusal and a token refresh.
- **F4 is closed.**
  - The HTTP route is removed, with the reason: `http.register` needs the spent `addrUnset`.
  - The "every byte" claim is narrowed to the connections a verified program can make: the client contracts' calls, and raw writes, which establish no protocol.
- **F5 is closed.** All five client contracts now name the raw listener and the empty gRPC server as answering no call successfully (the error arm).
- **No statement changed except F2.**
  - The five client contracts and `etcdSvc` have the same text.
  - `kvClientAt` is unchanged. The `KVClientDist.lean` additions (`putGetInvK` and its update lemmas) are definitions and theorems for the client theorems, outside the trust base.
- **Nit, optional.** Each client docstring still says "served only by `Serve_dist`" just before the new sentence about other programs. Read it as "answered successfully only by `Serve_dist`".

**Final verdicts.**

| Axiom | Verdict |
|---|---|
| `etcdSvc` | sound |
| `Serve_dist` | sound (F2 applied) |
| `KV_Put_dist` | sound |
| `KV_Get_dist` | sound |
| `KV_Delete_dist` | sound |
| `KV_Compact_dist` | sound |
| `Txn_Commit_dist` | sound |

No open findings.

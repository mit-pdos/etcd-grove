# Recheck of the client re-review findings (W0 NF1–NF3, 1c N1, 1d N1)

Reviewer: fresh, independent, read-only (2026-11-09). Worktree `specs-only`, HEAD `4a6a9b6b6e`, with
the repairs uncommitted in the working tree. Diffed against `4a6a9b6b6e`:
`Spec/go_etcd_io/etcd/{client,api}`, `Spec/context`, `examples/specreq/{clientv3kv,clientv3lease,concurrency}`.
Go sources: `.lake/src/{client,server}` (fork `a4d2bb17`). I wrote the verdicts below before reading the
"Re-review" sections of `repair-{client-core,client-users,grpc-v3rpc}.md`. I read them afterwards only to
check the one disagreement (RR-1).

`go vet ./specreq/clientv3kv/ ./specreq/clientv3lease/ ./specreq/concurrency/` passes.

## Verdicts

| batch | verdict |
|---|---|
| **W0** (client KV) | **PASS WITH OPEN DECISIONS.** C3 (the scope premise: no non-`nil` empty range end) and 1.5 (unissued tokens) stand. NF1, NF2 and NF3 are resolved. |
| **1c** (lease, ...) | **FAIL.** N1 is resolved: the false clause is gone. But the fix leaves `examples/etcd/leaseexpiry`, a named user of `lessor.TimeToLive`, with no proof (**RR-1**). C1, C4, C5 and 1.5 stand as before. |
| **1d** (concurrency) | **PASS WITH OPEN DECISIONS** (1.13 / C10). N1 is resolved, and the new snippet `ReqElectionNoTwoLeaders` closes. |

## The findings rechecked

| report | finding | status | evidence |
|---|---|---|---|
| R-A1 | **NF1**: the KV requests' `endsOk` had no source | **Resolved** | See (a) below. |
| R-A1 | **NF2**: `cloneCompare`/`FromCompare`/`Cmp.Clone` at a non-`nil` empty end | **Resolved** | See (b) below. |
| R-A1 | **NF3**: `Context.Value.spec` vs `ctxOk_of_isContext` | **Resolved** | The law is dropped (`Spec/context/Api.lean:95-97`), and nothing in `Spec/` or `examples/` names it. `Value.spec` (`:176-180`) is true of Go's contexts: a `valueCtx` compares the key with a stored key of a comparable type, so the comparison never panics. The second-tier `ctxValueIs_child` now takes a "not `*int`" premise (`:194-196`). That is right for `&cancelCtxKey`. It also excludes user keys of type `*int`, which is harmless (the same shape as Perennial's `notIntPtrKey`). |
| R-A2 | **N1**: `TimeToLive`'s per-member fact is false | **Resolved, but introduced RR-1** | See (c) below. |
| R-A3 | **N1** (1d): `ReqMutexNoTwoHolders` needs distinct leases | **Resolved** | See (d) below. |

**(a) NF1.**
- **The fix.** `rangeReqOwn_unfold`, `deleteReqOwn_unfold` and `compareOwn_unfold` (`api/v3/Wire.lean:374,410,443`)
  now carry `es = slice.nil ∨ ebs ≠ []`. Through `requestOneof` and `msgsOwn`, `requestOpOwn` and
  `txnReqOwn` carry it too. 3h's relation laws give `endsOk c` (`etcdserverpb/Api.lean:339-359`, and
  `reqOwn_msgAt` in `Realize.lean:78`), which is what `unaryArgs_msgAt` (`Realize.lean:212-221`) takes.
- **The builders discharge the conjunct:**
  - `Op.toRangeRequest`, `Op.toRequestOp` and `Op.toTxnRequest` take `o.emptyEnd = false`.
    `OpM.emptyEnd` (`client/v3/Api.lean:368-374`) is recursive over `thenOps`/`elseOps`, so
    `toTxnRequest` gets each sub-op's premise from its own.
  - Their only Go callers (`kv.go:171,219,242`; `txn.go:114,132`; `op.go:204,208,221,229`) all run
    under the KV triples' premise (`Api.lean:722,737,771,791,829,840`).
  - `kv.Do`'s inline `DeleteRangeRequest{RangeEnd: op.end}` (`kv.go:226`) has it from `DoTriple`'s premise.
  - The compares come from `cmpAt`, which is `optOwn compareOwn` and now carries the conjunct. Each
    constructor meets it:
    - `Value`, `Version`, `CreateRevision`, `ModRevision`, `LeaseValue` and `ensureCompare` leave the end `nil`;
    - `WithRange` takes `e ≠ []`;
    - `WithPrefix` uses `prefixEnd`, which is never `[]` (`Api.lean:216-219`).
- **Soundness.** No server-side regression:
  - Decoded messages get `endsOk` by `endsOk_canon` (proto3's implicit-presence `bytes` decode empty as `nil`).
  - The txn snippets' free `end []byte` is covered by their package's common assumption ("an empty
    RangeEnd is nil", `examples/specreq/txn/read.go:9`).
  - `endsOk_range_intro` stays sound.
  - The new `endsOk` for end-less requests (put, compaction, the non-KV ones) is plausible: `endsOk`
    names only the KV and watch-create ends. The auth `Permission.RangeEnd` is modelled as raw bytes,
    so `norm` keeps it.

**(b) NF2.**
- `cloneCompare.spec` is unchanged in text, but its premise `optOwn compareOwn` now excludes the bad end.
- **Proof plan.**
  1. `compareOwn_msgAt` gives `compareHolds c m ∧ endsOk c`.
  2. `Proto.Clone` gives `msgAt (norm c)`.
  3. `holds_norm` gives `compareHolds (norm c) m`.
  4. `norm_facts` (idempotence) with `endsOk_canon` gives `endsOk (norm c)`.
  5. `compareOwn_msgAt` from right to left gives the copy's `compareOwn` at `m`.

  The plan closes.
- `FromCompare` now has a scope premise that falls inside C3. The gRPC proxy, its user, holds decoded
  compares, so it meets the premise.

**(c) R-A2 N1.**
- `viaFact` (`ApiClient.lean:419-432`) and 2a's `leaseFact` (`v3rpc/Api.lean:319-333`) now give nothing for
  `.leaseTimeToLive`. They keep the clause for `Grant`, which is answered after the local apply, and for
  `Leases`. That matches the code: `LeaseLeases` answers from `s.lessor.Leases()` (`v3_server.go:737`).
- `ReqGoneNotListed` is rewritten over `Grant` and then `Leases` twice. It closes:
  1. the grant gives `leaseViewLb γ ep jg`;
  2. the first `Leases` answers at `j1 ≥ jg`, without `g`, and gives `leaseViewLb γ ep j1`;
  3. the second answers at `j2 ≥ j1`;
  4. a lease absent after its grant stays absent until it is granted again, which the snippet's
     `Assumes` excludes.
- `open-questions.md` A4 is corrected. **The fix is too strong for one user: see RR-1.**

**(d) R-A3 N1.**
- `NewSession.spec`'s grant branch (`NewSession.lean:78-81`) now names the grant's pre-state:
  `σg.leases id = none`, with `Reach σ0 σg` and `Reach σg σ`.
- **Provable.** `Lease.GrantTriple` gives `Q σ σ' res` of the answered step (`ApiLease.lean:240-243`).
  `NewSession` instantiates `Q` with the two lower bounds and `leaseStep`'s grant arm, which has
  `σ.leases id' = none` (`Model.lean:1075`). The post is only strengthened, so no caller breaks.
- `ReqMutexNoTwoHolders` closes. The first session's post state is the second call's `σ0`, and `id1`
  is still live at `σg2`, because there is no lease expiry and the new `Assumes` says no one else
  revokes the lease.
- **The new `ReqElectionNoTwoLeaders`** (`election.go:134-178`) closes:
  1. `k2 ≠ k1`, from the distinct leases;
  2. `k2` is absent at e1's post state (only e1 and e2 write under `pfx/`), so `Campaign`'s `σv`
     record gives `cr2` above `r1`;
  3. `waitedFor pfx k2 cr2 σ` (`Election__Campaign.lean:67-71`) is `noOlder` at `σ`;
  4. `k1` is present with create revision `r1`, because the atomic flag's invariant ties
     `resigned = false` to `k1` being present (only `e1.Resign` deletes it, and `campaignEff` keeps
     e2 off `k1`).

  An `e1.Resign` that fails only blocks e2's wait. That is a liveness matter, not a panic.

## New first-tier findings

### RR-1 (1c). With `TimeToLive`'s per-member clause gone, nothing proves `examples/etcd/leaseexpiry`

- **The user.** `examples/etcd/leaseexpiry/leaseexpiry.go:68-102` runs one member:
  1. it grants a lease;
  2. it polls `TimeToLive` until it answers not found (`TTL == -1 && GrantedTTL == 0`);
  3. it calls `Leases` and panics if the lease is listed.

  The package doc states "the theorem to prove is that it does not". `lessor__TimeToLive.lean:4` lists
  it under Users, and so do `ApiLease.lean`'s header and `State.lean:184` (`leaseViewLb`, "what
  `examples/etcd/{leasegrant,leaseexpiry,leasecatchup}` carry").
- **The step that no longer closes.**
  - `TimeToLive` now gives only `leaseStep`'s `∃ i, σ.leaseAnsAt i …` (`Model.lean:1087`): some table
    of the history, with no tie to the member.
  - `Leases` answers at `ep`'s table `j2 ≥ jg` (the grant's).
  - The model allows `j2 < jt`, where `jt` is the table at which `TimeToLive` found the lease gone. At
    such a `j2` the lease is still listed, so the panic is not excluded.
  - No law relates the leader's answer to `leaseViewLb γ ep`, even for a single member.
  - `ApiLease.lean`'s header and `repair-client-core.md` say the pattern "holds for its single member
    only" / "because its one member is the leader". No statement says so.
- **True of the code.** On a single member, `LeaseTimeToLive` answers from its own lessor. That is true
  when it leads (`v3_server.go:636-669`), and also before an election: it waits for a leader and
  forwards over HTTP to itself (`:671-676`). `Leases` then reads the same lessor later, so the guarantee
  holds and the spec is too weak (completeness, a named caller).
- **Suggested fix.** Restore the clause where it is true, as a gated row of the one spec (PRINCIPLES,
  "One spec, a gated row"). For example, in `viaFact` and `leaseFact`:

  ```
  | .leaseTimeToLive .. =>
      soleMember γ ep -∗ (⌜¬ leaseAnsRes res⌝ ∨ ∃ j, ⌜i ≤ j ∧ σ.leaseAnsAt j rq res⌝ ∗ leaseViewLb γ ep j)
  ```

  Here `soleMember γ ep` is a persistent fact that the single-member boot (`etcdstart.StartServer` /
  2e's bootstrap) gives and that no reconfiguration falsifies while it is held. A more general option
  is a leader-side view `leaseLeaderLb γ j`, with a law to `leaseViewLb γ ep j` when `ep` is the only
  voter. Either way, record it against A4, whose "Alt.: a single-member mode" is exactly this.
  Otherwise, drop `leaseexpiry` from the Users lists and from `leaseViewLb`'s doc, as a recorded
  decision.

## Regressions checked (files changed since `4a6a9b6b6e`)

- **`Wire.lean`, `etcdserverpb/{Api,Realize}.lean`.** Consistent, as in (a). The unfold and `msgAt`
  laws agree: under the new conjunct, `endOf` is `[]` or the bytes, so `[0]` arises only from a real
  `"\x00"`, and `endsOk` holds.
- **`Model.lean` `adminDenied`** (R-A6 N3). It is weaker, and sound. `jo` is unbounded, but so are
  `jf` and `jx`, which matches a stale member's local check. The compact arm's other errors are
  unchanged, so `ReqCompactReached` ("panics only on `ErrFutureRev`") still closes. No client snippet
  needs root's compaction to be accepted.
- **Stringer depth premises** (R-A6 second tier). Their users have the bound: range requests are at most
  3 deep (`holds_depth`); a transaction's depth is the server's to keep (2c). Owned by A6/A7; not rechecked in full.
- **`New`/`newClient`/`kubernetes.New`: `eps ≠ []` on success.** True: `client.go:87` refuses an
  empty list.
- **`NewSession`.** The post is strengthened; see (d).
- **Doc-only changes:** `ApiClient` `ctxPrin` (S-c), `Queue`/`PriorityQueue.Dequeue`, the
  `concurrency/Api` header.

**Uncertain, outside these batches (1b, unchanged).**
- `watchReqOwn_msgAt` (`Realize.lean:68-70`) gives no `endsOk`, while `holds_norm`'s watch clause
  requires it.
- Since `watchReqOwn_unfold` models the create's end as raw bytes (`createRange k e`), `norm` probably
  keeps the model anyway. In that case the clause's premise is unnecessary, and the gap is only in
  the statement.
- Worth a look by 1b/3h.

## Counts

- Findings rechecked: 5.
  - 4 resolved: NF1, NF2, NF3, 1d N1.
  - 1 resolved but introducing a new problem: 1c N1, giving RR-1.
- New first-tier findings: 1 (RR-1).
- New second-tier notes: 1, uncertain (the watch request's `endsOk`).
- No Go bug found. Nothing to add to `issues/`.

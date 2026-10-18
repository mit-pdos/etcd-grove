# Axiom audit (Lean port)

**Started:** 2026-10-18, branch `raft-retarget`. **Why:** the closed adequacy theorem (item 9)
is only as sound as the axioms it rests on, and the trust base (`etc/tcb-baseline.txt`, 327
axioms, 12 `sorry`s) has grown one names-only spec at a time. An axiom here is a claim about Go
code that nobody checked mechanically; a false one can make the closed theorem prove something
false of Go. This file records each axiom's verdict, the reason, and the fix.

## Verdicts

- **false**: the spec claims something the Go code does not do. Typically the code writes state
  that the spec frames out (state other resources own), or it panics or blocks where the spec
  says it returns. A false axiom is unsound, not just unproved.
- **suspect**: not shown false, but its argument needs checking. Examples: a proposal to raft
  that the spec does not restrict, a set of predicate laws with no model, a claim about another
  process.
- **ok**: the spec checked against the Go body (or the library's documented behavior) and holds.
- **benign**: a library spec whose content is trivially true or whose only effect is logging,
  formatting or metrics, with no ownership of shared state.

## Method

For each axiom: read the Go body at the pinned revision (`.lake/go-src/etcd/...`,
`.lake/go-src/raft/...`, or the library's source), list the state it reads and writes and the
calls it makes (including proposals to raft and sends on channels), and compare with what the
spec's precondition owns and its postcondition gives back. An axiomatized predicate's laws
(persistent, timeless, fractional, ...) must have a model: some interpretation in which every
law of that family holds at once.

## Known or likely problems (2026-10-18)

1. **`EtcdServer.compactRaftLog`: false.** The spec is `{srvLgReader s} … {srvLgReader s}`.
   The Go code (`server/etcdserver/server.go`, `compactRaftLog`) calls
   `s.r.raftStorage.Compact(compacti)`, which rewrites the `MemoryStorage`'s entries. The
   model gives those to raft's node goroutine (`ownMemoryStorage`), so the triple is false in
   the model. It runs once etcd's snapshot count of applied entries is reached, within the
   closed theorem's step bound.
2. **`EtcdServer.snapshot`: false.** The Go code calls `s.KV().Commit()`,
   `s.r.raftStorage.CreateSnapshot(...)` and `s.r.storage.SaveSnap(...)`; the spec owns none
   of the storage. Since D17d (`rnSnapOnce`), `MemoryStorage.CreateSnapshot` takes the
   application's snapshot token `memSnapTok`, which this spec does not take.
3. **Unchecked, same pattern possible:** `EtcdServer.applyConfChange` (frames only the conf
   change and `ep`'s conf state), `createMergedSnapshotMessage`, `sendMergedSnap`,
   `revokeExpiredLeases`, `raftRequestAlarm`, `Cleanup`, `stopWithDelay`, and `Start`'s
   monitors (`adjustTicks`, `purgeFile`, `monitorFileDescriptor`, `monitorStorageVersion`,
   `monitorKVHash`, `monitorCompactHash`, `monitorDowngrade`). A method that proposes to raft
   must be restricted in what it proposes, or the KV workload invariant (`kvInv`,
   `clusterWorkloadOk`) can break. D19c did this (`srvMonitorPermit`) for `publishV3` and
   `monitorClusterVersions` only.
4. **Large models, suspect until a model is shown:** bbolt's `*_kv` triples and the `backend.*`
   predicates with their laws (about 65); gRPC's serving and client axioms with their
   predicates (about 50). The risk is a family of laws that no model satisfies at once, which
   would let a proof derive `False`.
5. **Not yet in the baseline:** `EtcdGrove.goose_adequacy_start` (D19d),
   `EtcdGrove.initLb_of_spec` (D19e), `features.NewDefaultServerFeatureGate` (item 9 point 7;
   its predicate `isFeatureGate` was false of Go until 2026-10-18). No linked result reaches
   them yet; `Main`'s proof will.

## Plan

- **Phase A (read-only; started 2026-10-18):** a verdict for every axiom in
  `etc/tcb-baseline.txt` and the three of point 5, grouped by package in the table below, with
  the reason for each one that is not **benign**. Go bugs found on the way go in `issues/`.
- **Phase B (after `rnLogFits` and the `NewServer.spec` round, D19g, land):** fix the **false**
  axioms by giving each spec the resources its Go code touches, as D17d did for `Snapshot()`.
  For example, `MemoryStorage.Compact`/`CreateSnapshot` under the lock with the application's
  token, and a proposal permit for the methods that propose. Then re-prove the callers.
- **Phase C:** models for the **suspect** predicate families (bbolt/backend, gRPC), or a
  narrower set of laws.

## Table

(Filled by phase A.)

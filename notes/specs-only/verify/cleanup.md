# Second-tier cleanup (2026-11-09)

The items of `rereview-cleanup.md` (except the crash-story pass, done in `repair2-crash.md`), then the
second-tier items still open in `RR-{client,grpc-auth,raftlog-bbolt,raft-core,server-core}.md`.
Skipped by assignment: anything in the other agent's files (ApiBoot, etcdserver top-level, v3rpc
Http, storage/backend New/Durable, raft Model.lean, lease/leasehttp). No client-facing statement
changed meaning; one law was strengthened (`holds_norm`'s watch clause, see below).

| item | report | status | files |
|---|---|---|---|
| A10 N1 `MvccStorage` realization at `mvccFpM m`/`keyDataOfM m` | R-A10 | already fixed (`repair-backend-schema.md`, re-review) | |
| A10 N2 `backend__begin` cites `statSlot_wtx` | R-A10 | already fixed | |
| A10 N3 `ReqSnapshotFresh` reopen / `NewDefaultBackend` | R-A10 | already fixed (`writeDurable`, reopen through `openBackend`) | |
| A10 N4 `confStateSave_hook` margin | R-A10 | already fixed | |
| A5 `ReqBootstrapBytes` context bound | R-A5 | done: Assumes adds `len(ctx) < 2^40` (Marshal's `fits`), as `ReqMarshalDecode` | `examples/specreq/raftpb/snapshot.go` |
| A5 `fmtErrorf` admits every verb | R-A5 | not done: part of open decision C35; narrowing needs a model of the format string's verbs (or per-call-site format constants), not cheap or local | |
| A3 stale "pending"/"requested" Changes lines (Dequeue files) | R-A3 | already fixed (`repair-client-users.md`, re-review) | |
| A9 S2 `ReqApplyWrite` ignore-flag put of an absent key | R-A9 | already fixed (`apply.go:40`) | |
| A9 S4 thread-token wording (`ReqPromoteCheckpointer`, `ReqBoot`) | R-A9 | already fixed | |
| A2 S-a..S-e | R-A2 | already fixed (`repair-client-core.md`, re-review) | |
| A8 S3 `sendable` / consecutive `MsgApp` entries | R-A8 | done differently: no premise needed. `msgPts` carries `msgWf`'s index rule (a `MsgApp`'s entries numbered from `Index + 1`, `msgPts_msgAt`/`msgPts_unfold`), and the decoder's `msgEncodes` carries `msgIs`, so the last entry's `GetIndex()` is `m.index + |entries|` and the encoder's post is true as stated. `v2Frame`'s doc and the encoder's sketch now say so | `rafthttp/Api.lean`, `rafthttp/msgAppV2Encoder__encode.lean` |
| A8 S1, S2, S4, S5 | R-A8 | already fixed (crash pass, `repair2-crash.md`) | |
| watch request's `endsOk` (uncertain) | RR-client | done: `holds_norm`'s watch clause drops its `endsOk c` premise. A create's model takes the key and end as the slices' bytes (`watchReqOwn_unfold`, `es ↦*□ e`, `createRange`), so `nil` and empty map to the same model and `norm` keeps it. `watchReqOwn_msgAt` cannot carry `endsOk` instead: a client's `WithRange("")` watch has a non-`nil` empty end. The law is stronger; nothing used the premise | `api/v3/etcdserverpb/Api.lean` |
| stale `endsDecoded` text (`kvServer__RangeStream`, `v3rpc/Api.lean`) | RR-grpc-auth | already fixed (recheck RR3, `repair2-server.md`) | |
| stale `authHook` in snippets | RR-grpc-auth | done: `authBeCur` with `authBeHook` | `examples/specreq/auth/{check,admin}.go` |
| `authBeCur`'s realization vs `store.go:433` | RR-grpc-auth | done: the writer's half of the field `as.be ↦{1/2} be` (read without `beMu`), the other half in `beMu`'s invariant (checks under the read lock), `Recover` writes it with both under `beMu.Lock` | `auth/Api.lean` |
| `kvDelOk`'s "`applySnapshot`'s new store" | RR-grpc-auth | done: the server's closure passed to `lessor.Recover` (`server.go:1087`); boot: `kvstore.go:117`/`watchable_store.go:107` | `etcdserver/apply/Api.lean` |
| `srvCurBe`'s field share; `NewUberApplier`'s "`bemu`'s read lock" | RR-grpc-auth | not done: etcdserver top-level files (the other agent's). `NewUberApplier.lean:10` still says "`bemu`'s read lock for `s.be`" | |
| `ReqCompactApplied` laws line | RR-raftlog-bbolt | done: adds `raftLog_publish`, `logFloor_stored` | `examples/specreq/raftlog/ready.go` |
| `Open`'s unfired update with a locally held `boltState` | RR-raftlog-bbolt | done: a client note in `Open.lean`'s header | `bbolt/Open.lean` |
| `spec_del`'s `txBytes` → `key ↦*` | RR-raftlog-bbolt | not done: uncertain (the reviewer's word). Handing the callback `∃ dq, k ↦*{dq} kb` changes the internal spec and needs bbolt's realization to say the key bytes survive the nested `DeleteBucket` (page or node memory); bbolt's proof may unfold `boltTx` instead. For bbolt's proof to decide | |
| NR1 / NR2 | RR-raftlog-bbolt | first tier; already fixed (`ReqCompactApplied` Assumes; NR2 is in `backend/Durable.lean`, not mine) | |
| S-e `coreIdle_floor` | RR-raft-core | already fixed (`repair2-raft.md`) | |
| `logFloor_mono`'s `t'` gloss | RR-raft-core | done | `raft/v3/ApiLog.lean` |
| `ReqReadAfterWrite` header | RR-server-core | already fixed (`repair2-server-core.md`) | |
| `compactable_intro`'s "gate share" | RR-server-core | done (was requested of server-boot) | `api/v3compactor/Api.lean` |
| `Start` sketch, `srvStores_kv` wording, apply-side sketches | RR-server-core | already fixed (`repair2-server-core.md`); etcdserver top-level anyway | |

Counts: 27 items. 10 done (one of them differently: A8 S3), 14 already fixed, 3 not done (C35's
verb narrowing, the etcdserver top-level docstrings, `spec_del`'s key bytes).

Nothing turned out to be first tier. A8 S3 was reported as a false encoder post, but it is not:
`msgPts` already carries the index rule.

Build: `etc/specs-build.sh` on the 8 changed modules and their importers' leaves (`etc/importers.py --leaves`, `SpecPlan.Spec.*` only): `Build completed successfully (3586 jobs)`, 0 errors, run twice; both runs ended `specs-build: FAILED` with no error, i.e. its final `--no-build` check saw upstream modules the other agent was editing at the same time. `go vet`/`gofmt` clean on `specreq/{auth,raftpb,raftlog}`.

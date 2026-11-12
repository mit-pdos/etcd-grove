# Repairs after the second re-review: server-core (RR-server-core RR1-RR4, client-core's request 2)

Group `server-core`, 2026-11-09. Findings from `verify/RR-server-core.md` (RR1-RR4 and its second
tier), and the coordinator's added item (client-core's `repair2-client.md`, request 2: the lease
specs' per-member view). Go checked against `.lake/src/server`.

## Per finding

### RR1: five apply-side specs used `srvMember` without `srvStarted` — **fixed** (as suggested, plus one)

- `applySnapshot`, `applyConfChange`, `snapshotIfNeededAndCompactRaftLog`, `snapshot`,
  `compactRaftLog` now take `srvStarted s γ id`. **Also `shouldSnapshotToDisk`**: it reads
  `s.Cfg.SnapshotCount` (`server.go:1252`), which `start` writes (`:556`).
- Why `srvStarted` is needed even with RR2's `srvFields`: `applySnapshot`/`applyConfChange` read
  `s.r.transport` (`srvMember`'s, via `srvNode_member`); `snapshot`, `compactRaftLog`,
  `shouldSnapshotToDisk` read the two `Cfg` fields `start` defaults (`SnapshotCount`,
  `SnapshotCatchUpEntries`, `server.go:550-565`), now read-only in `srvStarted` (its docstring).
- Callers: `applyAll` (for `applySnapshot`, `snapshotIfNeeded…`) and `apply` (for `applyConfChange`)
  hold it; `snapshotIfNeeded…` passes it on. Each file has a `Changes: re-review (RR1)` line; the
  stale "comes from `srvNode_member`" sentence is marked superseded.

### RR2: getters before `srvMember` — **fixed** (option (a), with two differences)

- New in `ApiBoot.lean`: persistent `srvFields s γ id` (the server literal's read-only fields:
  `memberID`, `lgMu`/`lg`, `cluster`, `readych`, `Cfg` but the two `start`-defaulted fields;
  `0 < id < 2^64`), laws `srvFields_persistent`, `srvFields_id`, `srvMember_fields`. In
  `ApiApply.lean`: `srvNode_fields` (`srvNode s N id ⊢ srvFields s N.etcd id`) and `srvNode_kv`.
  Realizations updated (`srvMember` = `srvFields` + transport + `srvNode`; `srvBuilt` holds the two
  `Cfg` fields until `start`; `srvNode`'s list no longer claims `s.w`/`s.applyWait`, which are
  `srvStarted`'s).
- Over `srvFields` (was `srvMember`): `Logger`, `MemberID`, `FeatureEnabled`, `RequestTimeout`,
  `Cluster`, `ClusterVersion`. `srvMember` stays for `CutPeer`, `MendPeer`, `PauseSending`,
  `ResumeSending`, `RaftHandler` (and the post-start getters `AppliedIndex`, `Lead`, ... unchanged).
- **Differently: `Config`** moves to `isServer s γ` (not `srvFields`): it copies the whole `s.Cfg`,
  including the fields `start` writes, so before `start` it would race; its users (maintenance
  `Status`, etcdhttp health) hold `isServer`. (A soundness gap the reviewer did not list:
  `srvMember`'s realization claimed all of `Cfg` read-only, but `start` writes two fields.)
- **`KV.spec`**: premise `s.kv ↦□ w`, post `RET #w; True` (as suggested). Sources:
  `isServer_kv` (new, `ApiReq.lean`: the points-to with `srvWatchable s γ w`), `srvNode_kv`,
  `srvStores_kv`. `Watchable`'s, `NewUberApplier`'s sketches updated.
- **Also `newCorruptionChecker`**: dropped its `srvMember` premise (and the `γ`, `id` binders):
  `NewServer` calls it at `server.go:365`, before `srvMember`, and the body only stores `s`.
- `Process`, `NewServer` sketches name `srvNode_fields`/`srvFields`; statements unchanged there.

### RR3: `start`'s token and `srvMember` — **fixed**

- `start.spec` takes `srvMember s γ id ∗ threadTok`, returns `threadTok`.
- `Start.spec` takes `srvMember s γ id` (NewServer's post gives it); chose the premise over a law
  `srvBuilt ⊢ srvMember`. Its sketch now has C45's accounting (each `GoAttach` returns the caller's
  token, the goroutine runs on its fork's).
- The compactor's `Run` gives the token back: `Periodic.Run.spec`, `Revision.Run.spec` and the
  `Run` part of `isCompactor_methods` (`v3compactor/Api.lean`, server-boot's file, edited as the
  brief allowed: only the `Run` WP and its docstring sentence). Both loops are `go func()`
  (`periodic.go:105`, `revision.go:67`); `Periodic.Run` before the `go` only reads its settings.

### RR4: `NewServer`'s token — **fixed; one callee requested**

- `NewServer.spec` takes the caller's `threadTok` and returns it on both paths.
- `lease.NewLessor` (lease-auth's, edited as the brief allowed): returns the caller's `threadTok`;
  the run loop (`go l.runLoop()`, `lessor.go:245`) runs on its fork's own token. `lessor.Stop` now
  gives none back (`RET #(); True`), consistently: its only spec user is `Cleanup`, whose post never
  carried that token; `lease/Api.lean`'s run-loop prose and the snippet `lease/lessor.go`
  (`ReqNewLessor`'s header) updated. `mvcc/{boot,restore}.go` cite `NewLessor` without the token:
  unchanged.
- **Not closed by me: `auth.NewTokenProvider`** keeps the caller's token on success ("for the TTL
  keeper goroutine `enable` starts"), but that goroutine is a `go` of its own
  (`simple_token.go:188`) with its fork's token. Request below; until then `NewServer`'s returned
  token is not provable on the success path (said in `NewServer.lean`'s Changes).

### Client-core's request 2: the lease specs' per-member view — **fixed** (with a new bridge, requested)

- `ApiReq.lean`: `SrvCallTripleF … F` (outcome 1 also gives `F σ σ' res`); `SrvCallTriple` is now
  its instance at `F := True` (no other spec changes). `srvLeaseFact γ ep rq vi σ σ' res`: the same
  body as 2a's `leaseFact` (grant: `leaseViewLb γ ep` of the table after it; `Leases`: `¬
  leaseAnsRes ∨ ∃ j ≥ i, leaseAnsAt j ∗ leaseViewLb γ ep j`; `TimeToLive`: the same gated on W0's
  `soleMember γ`). `srvLeaseLbOpt γ ep vi` (the caller's optional bound).
- `LeaseGrant`, `LeaseLeases`, `LeaseTimeToLive`: `∀ ep` (and `vi` for the reads), premise
  `srvAt s γ ep` (and `srvLeaseLbOpt γ ep vi`), over `SrvCallTripleF … (srvLeaseFact γ ep rq vi)`.
- Go: `LeaseLeases` reads its own lessor (`v3_server.go:737`, no forwarding); `LeaseTimeToLive`
  answers from the leader's lessor after `waitAppliedIndex` (`:636-669`) or forwards (`:671-686`),
  so only under `soleMember` is it this member's lessor (its own peer URLs' `leasehttp` handler,
  same lessor); `Grant` returns after this member applied it (`raftRequest`'s apply wait).
- **The bridge `srvAt s γ ep`** (new, persistent, provisional, with `srvAt_agree`): 2c knows the
  member `s`, W0's `leaseViewLb` is per endpoint `ep`. Without it no 2c spec can give
  `leaseViewLb γ ep j`, and 2a's `Server.spec` is stated `∀ ep` (its `regsOk` for every `ep`), so
  as stated a lagging member's handlers could claim another endpoint's view. Realization:
  `leaseViewLb γ ep j := ∃ s, srvAt s γ ep ∗ (s's lessor reflected table j)`. Introduction
  requested of grpc-v3rpc/server-boot.

### Second tier

- `ReqReadAfterWrite`'s header (`etcdserverreq/read.go`): stale "assumed of 3e" caveat removed;
  cites `etcdLb_reach`, `srvWatchable_hist`, `isServer_kv`. **Fixed.**
- `Start`'s sketch: C45 shape. **Fixed** (RR3).
- `srvStores_kv`'s "lent out and back": the docstring says the closing wand returns only at the same
  `be`, `σ`, and `applySnapshot` rebuilds from the realization. **Fixed.**
- `compactable_intro`'s stale comment (`v3compactor/Api.lean:126`): server-boot's; **requested**.
- Apply-side sketches citing `srvNode_member` for `Logger`: **fixed** (RR1).
- `etcdserverboot/boot.go` `ReqStartOne`'s header: the token for `NewServer` and `Start`, `Start`
  with `srvMember`.

## Requests to lease-auth

1. `SpecPlan/Spec/go_etcd_io/etcd/server/v3/auth/NewTokenProvider.lean`: the success branch gives the
   caller's `threadTok` back (`tokenProviderAt … ∗ threadTok`); the simple token's TTL keeper is
   started by `enable` with `go t.simpleTokenKeeper.run()` (`simple_token.go:188`), a fork with its
   own token. Needed for `NewServer.spec`'s returned token (RR4).
2. `leasehttp`'s handler contract (for `LeaseTimeToLive` under `soleMember`): the answer is the
   serving member's lessor's, at or past its view (the per-member table `j`), so a forwarded
   `TimeToLive` to the member's own peer URLs gives `srvLeaseFact`'s row.
3. FYI: `lease/NewLessor.lean`, `lessor__Stop.lean`, `lease/Api.lean` (one prose sentence), and
   `examples/specreq/lease/lessor.go`'s `ReqNewLessor` header edited by me (RR4, as the brief
   allowed): `NewLessor` returns the caller's token, `Stop` returns none.

## Requests to grpc-v3rpc

1. `api/v3rpc/Api.lean`: identify `leaseFact` with 2c's `EtcdServer.srvLeaseFact` (same body), as
   `firedAns` is `srvFiredAns`; the lease handlers call 2c with `srvAt s γ ep` and pass the
   contract's `leaseViewLb γ ep i` as `srvLeaseLbOpt γ ep vi`.
2. `api/v3rpc/Server.lean`: `regsOk B (etcdContract γ ep) …` only for the `ep` the server is bound
   to, under `srvAt s γ ep` (not `∀ ep`), or a law introducing `srvAt` where `Grpc.start` binds
   `addrAt ep` (with one member per address, `srvAt_agree`).
3. Sketches citing `KV.spec`'s old post (`header__fill`, `newHeader`, maintenance `Rev`/hashes):
   `isServer_kv` first, then `KV.spec` at that points-to. `Config.spec` is now over `isServer`.

## Requests to server-boot

1. `api/v3compactor/Api.lean:126` (`compactable_intro`'s comment): "its `isServer` and gate share
   from `R`" is stale (`Compact` takes no gate at `phys = false`).
2. FYI: `isCompactor_methods`' `Run` WP and `Periodic.Run.spec`/`Revision.Run.spec` now return
   `threadTok` (RR3).
3. The introduction of `srvAt s γ ep` if it belongs to the serving start (`etcdstart`'s `Serve`,
   embed's `serveClients`) rather than to 2a's `Server`.

## New decisions

- **`srvAt s γ ep`, a member-to-endpoint bridge.** The lease rows are per endpoint (W0's
  `leaseViewLb γ ep`), the server specs per member. I added a persistent, agreeing `srvAt` that the
  lease specs take; its introduction belongs to whoever binds the gRPC server to `ep`. The
  alternative, a member-indexed view `srvLeaseLb s j` with a 2a law converting it, moves the same
  bridge to 2a. Either way 2a's `Server.spec` (`∀ ep`) must stop proving the contract for every
  endpoint.
- **`Config()` over `isServer`.** A getter that was available from `NewServer` on is now only after
  `Start`, because `start` writes two `Cfg` fields; the code's users are all post-start. The
  alternative is a fork change (default the fields in `NewServer`), not needed.
- **The lessor's run-loop token** is no longer a loan returned by `Stop`: the fork's own token
  serves it (`NewLessor` returns the caller's). This removes a token `Cleanup` silently dropped.

## Build

`etc/specs-build.sh --dir` on `etcdserver/` (top level), `lease/`, `api/v3compactor/`: all modules
built. The importers (`etc/importers.py --leaves` of `ApiBoot.lean` and `lease/Api.lean`: 621
leaf modules, which cover every module importing my changes, v3rpc, apply, txn, the snippets' specs)
built with no error three times (`Build completed successfully (3095 jobs)`); `specs-build.sh`'s
final `--no-build` check reported FAILED each time only because other agents were editing upstream
modules meanwhile (`api/v3/State.lean`, `rafthttp/Api.lean`, `snap/Api.lean`: out of date, not in
error). `go vet` clean: `specreq/etcdserverreq`, `etcdserverboot`, `lease`.

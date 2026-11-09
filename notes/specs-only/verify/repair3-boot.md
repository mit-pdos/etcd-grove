# Repairs, third round: server boot and around (repair3-boot)

2026-11-09. The requests in `repair2-client.md` (to server-boot), `repair2-relay.md` (to server-boot
and server-core), `repair2-crash.md` (to grpc-v3rpc, raft-core, backend-schema, server-core) and
`repair2-server-core.md` (to server-boot). Go checked against `.lake/src/server`.

## Per item

### 1. `urlsReserve` (client-core's RR-1 request): fixed

- `ApiBoot.lean`:
  - `cluster_alloc.spec` now also gives `urlsReserve γ 1`.
  - `urls_reserve.spec` takes a share `urlsReserve γ q` and does not give it back.
  - So `soleMember_intro` has its source.
- **Realization.**
  - The cluster's reservation invariant holds the spent shares beside the minted `urlsRight`
    entries.
  - An entry exists only if some share was spent. So holding the whole share outside means no entry
    exists.
  - `soleMember` is the persistent invariant that holds the given-up `urlsReserve γ 1`, with
    `memberBoot`'s record that the initial members were `[m]`.
- **Users.** No Lean statement uses either law: only snippets cite them, as Assumes text.
  - I updated `etcdserverboot/boot.go`'s `ReqJoin` and `clientv3client/cluster.go`: a reservation
    spends a share.
  - The others (`ReqStartOne`/`ReqStartThree`, `raftnode/restart.go`, `raftcore/ready.go`) only
    allocate, so they are unaffected.

### 2. `srvAt s γ ep` introduction (relay request 1): fixed, keyed by member id

- **New in `ApiBoot.lean`:**
  - `srvEp γ ep id`: opaque and persistent. The client address `ep` belongs to member `id` of `γ`
    for the whole run.
  - Its laws: `srvEp_persistent`, `srvEp_agree` (`γ = γ' ∧ id = id'`), `srvEp_gen` (`⊣⊢` at
    `L'`), and `srvEp_reserve : Http.addrFree ep ⊢ |==> Http.protoAt ep P ∗ srvEp γ ep id`.
- **`srvAt` moved from `ApiReq.lean` to `ApiBoot.lean`** and is now transparent:
  `srvAt s γ ep := ∃ id, srvFields s γ id ∗ srvEp γ ep id`.
  - `srvAt_persistent` stays.
  - `srvAt_agree` (`s = s'`) is replaced by `srvEp_agree`.
  - `ApiReq.lean` keeps a pointer comment.
- **Restarts.** `srvAt` is not per-generation and has no `_gen` law. A restarted member, after a
  stop or a crash, is a new `s` with its own `srvFields`, at the same `ep` by `srvEp` (and
  `srvEp_gen` after a crash).
  - The old `s = s'` agreement was false of a stop-and-restart within one generation (boot.go's
    restart snippet serves the member again).
- **Why member-keyed is sound.** W0's `leaseViewLb γ ep j` is realized as member `id`'s lessor
  view. That view only moves forward over the member's life in a generation:
  - a stop's `backend.Close` commits the batch (`backend.go:470-471`);
  - the restart's lessor is recovered from that backend.

  It does not survive a crash, since the lost batch may hold applied grants. So W0 has no
  `leaseViewLb_gen`, and none must be added.
- **Realization of `srvEp_reserve`**, as `cluster_alloc`'s use of `addrFree`: net/http's intended
  global map from addresses to saved protocols keeps the reserver's tag `(γ, id)` beside the
  protocol.
- **Snippets.** `v3rpc/serve.go`'s Assumes now name `srvEp_reserve`, `srvEp_gen` and
  `Http.protoAt_gen`. `etcdserverboot/boot.go`'s `ReqCrashRecover` lists `srvEp_gen` and
  `protoAt_gen`.
- **Text updates.** The docstrings of `v3rpc/Server.lean` and `v3rpc/Api.lean` now name
  `srvEp_reserve` (text only).

### 3. `leaseURLOf` introduction (relay request 2): fixed, under the existing deployment premise

- **New law**, `ApiBoot.lean` `leaseURLOf_intro`: for `m ∈ σ.members` (with `etcdLb γ σ`), `u ∈
  m.peerURLs`, `srvEp γ ep m.id` and `Leasehttp.leasePeerURL (u ++ "/leases/internal")`, it gives
  `Leasehttp.leaseURLOf γ ep (u ++ "/leases/internal")`.
- **Why it is true.**
  - Peer-URL sets are single-use over the run, so `u`'s handler belongs to member `m.id`.
  - `leasePeerURL` is the trusted premise that `TimeToLiveHTTP` already takes: embed's
    `etcdhttp.NewPeerHandler` mounts `s.LeaseHandler()` at `/leases/internal`
    (`etcdhttp/peer.go:44-71`).
- **`ApiBoot` imports `leasehttp/Api`.** There is no cycle.
- **`Leasehttp.leaseURLOf` had no heap binders.** It was declared with only `(γ ep url)` inside a
  section. It now carries them explicitly, like `raftProto` in the crash pass. Its header points
  at the law.
- **Not true of this repository's starters.** See New decisions 1.

### 4. server-core

- **`EtcdServer__leaseTimeToLive.lean`** (the assumed contract) changed:
  - It takes `ep`, `vi`, `srvAt s γ ep` and `srvLeaseLbOpt γ ep vi`.
  - Its success outcome gives the gated row `⌜¬ leaseAnsRes res⌝ ∨ (soleMember γ -∗ ∃ j σ₂, ⌜i ≤ j ∧
    σ₂.leaseAnsAt j rq res⌝ ∗ etcdLb γ σ₂ ∗ leaseViewLb γ ep j)`.
  - A Changes block gives why it is true on both paths (leader: `Lookup`; forwarding: `waitLeader`
    is the member itself, then `leaseURLOf_intro` and `ltlView`). It also says that the deployment
    premise fails for `etcdstart`.
- **`EtcdServer__LeaseTimeToLive.lean`**: the sketch now names that row as `srvLeaseFact`'s source,
  taken to the firing state by `etcdLb_reach`.
- **`EtcdServer__applySnapshot.lean`**: the Changes line names the revert list (`Backend.beRevs` /
  `Snap.revertSt`, `o :: os`) and the backend steps of item 7. It also records a gap found doing it
  (New decisions 3).

### 5. grpc-v3rpc: `Http.protoAt_gen` and `addrFree_gen` fixed

- Both laws are `⊣⊢` at `L'`, in `Spec/net/http/Api.lean`'s laws, which now list them.
- **Realization:** the intended global map, in `GooseGlobalGS`. The protocol is a saved value, the
  same `P` on both sides.
- `rafthttp/Api.lean`'s `peerAddr_gen` docstring now cites `protoAt_gen` (text only).

### 6. raft: fixed

`Model.lean`'s `Durable.crashed` docstring now says:
- it is the no-snapshot case;
- a snapshot batch is covered when nothing or all of it is written (`Durable.crashOk`,
  `raftState_crash`).

### 7. backend-schema: both requests fixed, with two gaps recorded

The design: the file moves between the client's crash state and the backend's at two atomic steps,
both ghost steps.

- **New vocabulary** (`backend/Api.lean`):
  - `beFileN`, the namespace of the backend's file invariants;
  - `beOpenUpd p o ns R`, an AU from `beFile p o` to `beDurInv γ p ∗ beSynced? ∗ beHist γ [I]`;
  - `beCloseUpd γ p Q`, an AU from `beHist γ L` to `beFile p (some I)` with `L.getLast? = some I`.
- **`beNew` no longer holds `beHist`.** The open's update puts it in the client's crash state.

**Request 1: `New` takes the file through an update at bbolt's open.**
- **4c's `Open` supports it.** It takes `boltFile γ ∗ boltClosed γ` and keeps the file in
  `boltFile`'s crash invariant throughout (an error closes it again; `dbOpenOk` excludes errors).
- So the update fires at the ghost step before `bolt.Open`: `fileHolds_alloc` plus the history's
  allocation.
- **Statements changed:**
  - `New.spec` and `newBackend.spec`: `beOpenUpd … R` in place of `beFile`, and the step takes `R γ`;
  - `storage/OpenBackend.spec`: the same;
  - `storage/OpenSnapshotBackend.spec`: the rename's update also puts the renamed `beFile p (some
    img)` in the caller's state, and `Q (some img)` gives `OpenBackend`'s `beOpenUpd`.
- **Text updated:** `Durable.lean`'s header, `bootstrap.lean`, `NewServer.lean`, the `ReqCrashRecover`
  Assumes (the window exclusion is removed), `backend/commit.go` and `more.go`.

**Request 2: `beCrash` did not hold after `Close` returned.**
- Close's post gave the file's OsFs resources away as `beFile p (some I)`, through 4c's
  `boltRelease`, which cancels `boltFile`. The client still held `beDurInv ∗ beSynced ∗ beHist`, and
  `beCrash`'s realization needs those resources.
- **The fix:** `backend.Close.spec` takes `beCloseUpd γ p Q` and posts `beFinal γ I ∗ Q I`. The
  update fires at the release after `DB.Close`. It takes the history (freeing its authority's
  `boltState` share for `boltRelease`) and gives the closed file at the same step.
- **2e's closers changed with it:**
  - `bootstrapped{Backend,Storage,Server}.Close.spec` take `beCloseUpd γb path Q` and post
    `beFinal γb I ∗ Q I`;
  - `beClosable` takes `γb` as a parameter.
- **Text updated:** `srvClosed`'s docstring.

**Recorded, not fixed:**
- **(a) A file created in this generation is not `beFile p (some I)` after its close.** That is
  etcd's first boot's `member/snap/db`, which `bolt.Open` creates with no directory fsync
  (`BoltSt.named = false`). `fileHolds_image` needs the name durable, and the old post had the same
  problem. It matters for a restart within the same generation after a first boot.
- **(b) applySnapshot** (New decisions 3).

### 8. server-boot: `compactable_intro`'s stale comment, already fixed

`v3compactor/Api.lean:126-131` already reads "no gate share at `phys = false`" ("Verify-round
cleanup, RR-server-core"). Nothing to do.

## Requests

### To client-core (W0, `api/v3/State.lean`)

`urlsReserve`'s docstring still says "requested of server-boot". It can say "`cluster_alloc` gives
it whole, `urls_reserve` spends a share (2e)". Text only.

### To the coordinator

- **New decisions 1 to 3 below.**
- **`top.md` K6** (the crash pass's replacement text) still lists "a crash inside the backend's
  open" as a recorded gap. That gap is closed. Two gaps replace it: (a) and the applySnapshot one
  (New decisions 3).
- **`open-questions.md` 3.2 / C24:** `etcdstart` should serve `s.LeaseHandler()`, which gives a
  reason to specify it (New decisions 1).

## New decisions

1. **The `soleMember` `TimeToLive` row is false for this repository's starters. This is a finding in
   our specs, recorded here.**
   - **The cause.** `examples/lib/etcdstart` serves only `s.RaftHandler()` on the peer address. A
     `TimeToLive` forwarded to its own peer URL gets rafthttp's mux `404`, and
     `leasehttp.TimeToLiveHTTP` turns that into `lease.ErrLeaseNotFound` (`http.go:263-264`).
   - **When it happens.** A sole member forwards only when it is not the leader at the
     `s.isLeader()` check (`v3_server.go:637`); then `waitLeader` returns itself. That is reachable
     before the first election of a server object. So consider a sole member restarted after a
     stop, in the same generation, at the same `ep`, and asked before its first election. It answers
     `ErrLeaseNotFound` for a lease a client saw at `ep` (`leaseViewLb i` with the lease present).
     The row says the lease is in a table `j ≥ i`, so it is false.
   - **Why the spec looked fine.** The contract's deployment premise `leasePeerURL`, now also
     `leaseURLOf_intro`'s, is false of `etcdstart`'s URLs. So the row rests on an unmet assumption.
   - **leaseexpiry in practice.** It starts once and asks after a grant. A single voter, once it
     leads, keeps leading, so it is not affected in practice. But its proof chain (RR-1) has no
     sound 2c source under `etcdstart`.
   - **The fix is the harness's.**
     - Serve a mux with `s.RaftHandler()` at `/raft`, `/raft/` and `s.LeaseHandler()` at
       `/leases`, `/leases/internal`, as `etcdhttp.newPeerHandler` does.
     - Write a spec of `EtcdServer.LeaseHandler` that makes `leasePeerURL` derivable (3.2, C24).
     - Until then, leaseexpiry's TimeToLive check is unproved at 2c.
   - I did not change `examples/lib` (shared; its header says it calls only what has specs).
2. **One member id per client address over the run** (`srvEp`), like peer-URL sets: a removed
   member's client URL cannot serve a new member.
   - **Why it is needed.** The lease view `leaseViewLb γ ep` is persistent and per address. A
     different member later serving `ep` could answer from a lessor behind it.
   - **The alternative**, a per-generation binding, would need a per-generation exclusive token for
     the address, which nothing issues.
3. **applySnapshot's backend swap is not covered by 4a's crash laws.**
   - **The problem.** The old backend is still open at the rename: `server.go:1068` opens the new
     one, and `:1144` closes the old one after the install. So:
     - the disk holds its open crash state, not the closed `beFile p o` that the rename's update
       takes;
     - its `Close` releases a file no longer named `p`, which `beCloseUpd` misstates (as the old
       post did).
   - **What it needs:** 4a laws for an open backend that is renamed over (its history becomes the
     revert entry), and for a close of an unlinked file.
   - **Recorded** in `EtcdServer__applySnapshot.lean`. It is not fixed: it is 4a's and 2d's design.

## Build

`etc/specs-build.sh` over `etc/importers.py --leaves` of every changed vocabulary module (net/http
`Api`, `leasehttp/Api`, `backend/Api`, `Durable`, `ApiBoot`, `ApiReq`, raft `Model`, rafthttp `Api`),
which covers every changed spec file: **OK (1738 modules)**, `Build completed successfully (4252
jobs)`, no errors. Snippets: `go vet ./specreq/{etcdserverboot,backend,clientv3client,v3rpc}/` passes, and
`gofmt -l` prints nothing.

# auth-lease S4: `etcd_authlease_safe` for k members (Draft, rev 1, 2026-11-16)

For etcd-grove-02 and the user. Branch `auth-lease-s4` (worktree `/shared/etcd-grove-rs56`, off lean `6a63774988`,
authN landed). Stage decided by the user and etcd-grove-81: the closed theorem `etcd_authlease_safe` for `k`
members, `1 ≤ k ≤ 1000`, on authN's generic auth start (`etcdstart.StartMembersAuth`), with leases at auth on: the
client's leased put (`WithLease`, `Put`/`Txn` with a lease), linearizable client specs of `Lease.Grant`/`Revoke`
(S3a's F3), the read handlers at auth on, `memberBootOn`'s `lg = false` dropped, and the C5′ lease-contract pair
merged. Background: `notes/auth-lease-scope.md` §1 (the checks), §7 (the multi-member variant: what a follower does
with each lease method, E10–E12), `notes/authN-draft.md` (the statement this one extends).

This Draft is a HARD STOP: the statement (§2) and the changes to exported text (§3) go to the user. Nothing outside
`examples/etcd/authlease/` (Go) and `Scratch/` (untracked probe) is written yet.

## 0. Summary

- **Program** `examples/etcd/authlease` (written, Go tests pass, §1): authN's start for `k` members; authkv's
  set-up through member 0; a barrier at every member; **root grants `Lz` and puts `z/lease` with it (member 0); `u`
  grants `Lu`, puts `a/lease` with it, and puts `a/txn` with it in a transaction (member `1 mod k`)**; a second
  barrier; then scope §1's checks 1–5, each principal through its own member; then `u` revokes `Lu` and root finds
  `a/lease` and `a/txn` gone. Sequential: one goroutine issues every request.
- **Statement** (§2): `etcd_authN_safe`'s, at the new program, plus three premises: `leaseIdsApart ids` (the
  15-bit member-id condition, Go-tested), `lease.leasesNoExpiry` and `leasePeersOk` (both existing opaque premises
  of the lease theorems). Result `Ok` or `Failed`, no stuck thread, no panic.
- **Token** (§6): `authlease-3354335`, the first `authlease-<n>` whose first 1000 members' ids are 15-bit
  distinct (and 16-bit nonzero); `TestMemberIDs` checks it. Needed because two members grant (0 and `1 mod k`).
- **Exported text that changes** (§3): no closed theorem. The client's auth-on Put/Txn specs drop their
  no-lease filters; the client lease library's specs move to the metadata form; a new linearizable lease
  contract and a served result for the read handlers; the C5′ pair merged (seven client results restated);
  etcdstart's auth start takes a lease mode.
- **Trusted text: none new** (§5).
- **Estimate** 19–30 agent-days (§7). **Decisions** D1–D9 (§9), each with a recommendation.

## 1. The Go program and its tests

`examples/etcd/authlease/authlease.go` (≈ 330 lines with comments), `authlease_test.go`.

**What it runs.** `Main(k)`: `k = 0` → `Failed`; `etcdstart.Members("authlease", k, 16000, 17000)` (member `i` is
`authlease-i`, peer `127.0.0.1:(16000+i)`, client `127.0.0.1:(17000+i)`); `etcdstart.StartMembersAuth(ms,
"authlease-3354335", NoSnapCount, NoSnapCatchUp, lg)` (authN's start, unchanged); then `run`:

| step | who, member | what | on error |
|---|---|---|---|
| serve | every member | `etcdstart.Serve` (gRPC) | `Failed` |
| set-up | no token, 0 | `auth.SetUp` (authkv's: root; role `r` READWRITE `[a, b)`; `u` with `r`; `v` without; auth on) | `Failed` |
| barrier 1 | root, every member | linearizable `Get(z/barrier)` | `Failed` |
| lease set-up | root, 0 | `Lz := Grant(600)`; `Put(z/lease, WithLease(Lz))` | `Failed` |
| | `u`, `1 mod k` | `Lu := Grant(600)`; `Put(a/lease, WithLease(Lu))`; `Txn.Then(OpPut(a/txn, WithLease(Lu)))` | `Failed` |
| barrier 2 | root, every member | as barrier 1: every member's lessor holds the three keys | `Failed` |
| check 1 | no token (0); invalid token (`1 mod k`) | `Grant`, `Revoke(Lu)`, `TimeToLive(Lu)` with and without keys, `Leases`: refused | panic |
| check 2 | `u`, `1 mod k` | `Put(a/x, WithLease(Lz))` and the same in a `Txn`: refused; root's `Get(a/x)` (0) finds nothing | panic |
| checks 3, 4 | `u`, `1 mod k` | `Revoke(Lz)`, `TimeToLive(Lz, WithAttachedKeys)`, `Leases`: refused | panic |
| check 5 | `v`, `2 mod k` | `Revoke(Lu)`, `TimeToLive(Lu, WithAttachedKeys)`, `Leases`: refused | panic |
| check 3' | root, 0 | `Get(z/lease)`: one key, attached to `Lz` | panic (an error: `Failed`) |
| revocation | `u`, `1 mod k` | `Revoke(Lu)`: must succeed | `Failed` |
| check 6 | root, 0 | `Get(a/lease)`, `Get(a/txn)`: no key | panic (an error: `Failed`) |

**How leases and auth mix.** Every lease row of `notes/auth-matrix.md` but `KeepAlive` is exercised: grant (token
required), revoke (write on every attached key, checked at apply on every member), leased put at top level and in a
transaction (write on every key the lease holds, at apply), `TimeToLive` with keys and `Leases` (read on the keys,
checked by the receiving member against its own lessor before any forwarding, scope §7.1). The raft-path rows
(revoke, leased put) are proposed at a follower whenever `k ≥ 2`; the lessor-local rows (`TimeToLive`, `Leases`) run
at a follower for `u` and `v` when the leader is elsewhere. Grants go through two members (0 and `1 mod k`), so two
members' id prefixes collect lease ids (§6). The positive steps (check 3', the final revocation, check 6) need the
linearizable lease specs (F3): the grant puts `Lz` into the client's model, the leased put attaches `z/lease`, a
refused revocation leaves the model, a granted revocation deletes the attached keys.

**What is not in it.** authkv's `Work` (the KV rows: authN has them; mixing both would double the proof without a new
row); `KeepAlive` (D2: a stream, whose auth-on serving and client `KeepAliveOnce` spec are not there; the test
checks its refusals at every member, so the decision can go either way); expiry (no lease expires: TTL 600 s, the
run takes ≈ 15 s; the premise `leasesNoExpiry`); concurrency between principals (the checks are sequential: the main
thread owns the client's model, which is what makes the lessor-side refusals provable, §4.3).

**Followers' forwarding** (scope §7.1, E10). With the examples' peers (raft handler only) a permitted `TimeToLive` at
a follower reports the lease absent; the driver makes no permitted `TimeToLive`, and the refused ones are refused by
the receiving member before it forwards.

**Tests** (`GOWORK=off`, `PATH=/usr/local/go/bin:$HOME/go/bin:$PATH`, under `systemd-run --scope -q -p
MemoryMax=32G`; etcd at the examples' `go.mod` pin `6e8f0c004c15`):

- `TestMemberIDs`: for the 1000 members, the ids etcd computes (`membership.NewMember`, checked against
  `NewClusterFromURLsMap`) have distinct nonzero 16 low bits (putgetN's `BootFacts`) and distinct 15 low bits
  (`leaseIdsApart`); the ids of `k ∈ {1, 2, 3, 7, 500}` members are a prefix. Passes.
- `TestMembers`: names and addresses at `k = 3`; `Main(0) = Failed`. Passes.
- `TestMainRun`: `Main(k)` for real (`AUTHLEASE_MEMBERS` or a random `k ∈ {1, 2, 3, 5, 7}`), must return `Ok`; then
  at every member: `u`'s `TimeToLive(Lz, keys)`, `Leases`, `Revoke(Lz)`, `KeepAliveOnce(Lz)`, `Put(a/x, Lz)` and `v`'s
  `Leases` fail with `permission denied`; the token-less client's `Grant`, `Leases`, `TimeToLive`, `KeepAliveOnce` with
  `user name is empty`; the invalid token's `Grant`, `Revoke` with `invalid auth token` (so the driver's refusals are
  the auth checks, not timeouts); a lease granted through each member has bits 48–62 equal to that member id's 15
  low bits (§6); `z/lease` still attached to `Lz`, the other three keys absent.
- **Results** (`/shared/tmp/auth-lease-s4/runs.log`): `TestMemberIDs`, `TestMembers` pass; `TestMainRun` passed **18 of 18** runs: `k ∈ {1, 2, 3, 5, 7, 9}`, three rounds each, plus two earlier runs at `k = 1, 3`; `Main(k)` takes 13.8–16.6 s whatever `k`.

No failure; nothing that looks like an etcd bug.

## 2. The closed statement

```lean
theorem etcd_authlease_safe [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.authlease.Assumptions]
    [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]
    [_root_.Perennial.errors.Assumptions] [_root_.Perennial.fmt.Assumptions]
    [go_etcd_io.etcd.api.v3.v3rpc.rpctypes.Assumptions]
    [go_etcd_io.etcd.client.v3.DialWithBalancerBody] [log.NewModel]
    (Hctx : ∀ hG, ContextReadErrs (hG := heapAt hG lctx))
    (Hcec : ∀ hG, ContextErrsClient (hG := heapAt hG lctx))
    -- (D22) the auth store's backend with auth on: trusted text, a named hypothesis (authN's)
    (hD22 : ∀ hG, ⊢ authSchemaSrv (hG := heapAt hG lctx))
    (k : Nat) (hk1 : 1 ≤ k) (hk : k ≤ 1000)
    (ids ps : List w64) (ctxs : List (List w8)) (boot : List LogEntry)
    (Hlen : ids.length = k) (Hbf : etcd_putgetN.BootFacts ids ps ctxs boot)
    -- NEW: the members' ids 15-bit distinct (lease-mono3 step 2's premise; `TestMemberIDs`)
    (Hap : leaseIdsApart ids)
    (Haf : authRecordsFit) (Hbuq : apply.backendUnderQuota) (Hrf : grpcRepliesFit)
    (Hdbo : storage.diskOk)
    -- NEW here, as `etcd_leasegrant_safe`/`etcd_leasecatchup_safe`: peers answer `/leases/internal`
    -- as etcd's handler does or not with 200; no lease granted in the run expires before it ends
    (Hlp : leasePeersOk) (Hlne : lease.leasesNoExpiry)
    (HNs : prometheus.namesUnclaimed (authleaseProgram k) authleaseNames)
    (HAs : addrsUnclaimed (authleaseProgram k) (etcd_authlease.authleaseAddrs k))
    (HDs : dataDirsAbsent (authleaseProgram k) (etcd_authlease.authleaseDirs k))
    (HEnv : verifyEnvOff (authleaseProgram k))
    (n : Nat)
    (Hprem : ∀ hG, ⊢ etcd_authlease.premises (hG := heapAt hG lctx) k n ids ps ctxs boot)
    (σ : state) (g : GlobalState) (Hlctx : σ.goState.goLctx = lctx) (Hinit : IsInit σ)
    (Hthreads : σ.threads = 1)
    (κs : List Observation) (t2 : List Expr) (σ2 : CfgState)
    (Hsteps : RealNsteps n ([authleaseProgram k], ((σ, g) : CfgState)) κs (t2, σ2))
    (Hn : n + 2 ≤ 2 ^ 28) :
    (∀ v t2', t2 = Val v :: t2' → v = #(W64 0) ∨ v = #(W64 1)) ∧
    (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
    (∀ v, Val v ∈ t2 → v.isPanic = false)
```

`authleaseProgram k := authlease.initialize' #() ;; Main #(W64 k)`; `authleaseAddrs k` the `2k` addresses (peer and
client of each member); `authleaseDirs k` the `k` directories `authlease-i.etcd`; `authleaseNames` the read package's
two metric names (authN's); `etcd_authlease.premises k n ids ps ctxs boot` is authN's `premises` at the token
`authlease-3354335` (per member `etcdstart.bootPremiseOn` with `AuthToken = "simple"` at putgetN's `dirN`;
`bootMarshal`; `etcdstart.commonPremises`). The ghost-state bundle: authN's `putgetGF` if it holds the lessor's
functors, else a bundle of its own (a form, decided at linking).

**In plain words.** For every member count `k` from 1 to 1000: run the program from a fresh state with one thread for
any number `n` of steps (`n + 2 ≤ 2^28`). Then the main thread, if finished, returned `Ok` or `Failed`; no thread is
stuck; no thread panicked. Not panicking means: after the set-up and the lease set-up, with every member past both,
every member a principal uses refused the client with no token and the client with an invalid token every lease
method; refused `u` a leased put (top level and in a transaction) with root's lease `Lz`, the revocation of `Lz`, and
`TimeToLive` with keys and the listing while `Lz` holds a key `u` may not read; refused `v` the same against `u`'s
lease; root afterwards found `z/lease` attached to `Lz` and no `a/x`; and once `u`'s own revocation of `Lu` succeeded,
root found the keys `Lu` held deleted. This holds if:

1. etcd's member ids for the `k` members (`ids`, in member order), the peers in `bootstrap`'s order (`ps`), their
   contexts and the boot log are what Go computes; the ids' 16 low bits are distinct and not 0 (`BootFacts`,
   putgetN's) **and their 15 low bits are distinct** (`leaseIdsApart`: two members whose ids agree there generate
   colliding lease ids, `issues/etcd-lease-id-mask-member-prefix.md`); `TestMemberIDs` checks both for every
   `k ≤ 1000` at the token;
2. the size facts authN assumes (auth records fit, the backend under quota, gRPC replies fit, the disk behaves);
3. **no lease granted in the run expires before it ends** (`lease.leasesNoExpiry`, the deployment premise of
   `etcd_leasegrant_safe` and auth-lease Q2: the TTL is 600 s, the run seconds) and **a peer answers the lessor's
   `/leases/internal` as etcd's handler does, or not with 200** (`leasePeersOk`, `etcd_leasecatchup_safe`'s; true of
   the examples' peers, which answer 404, E10);
4. at start nothing else claims the program's metric names, its `2k` addresses or its `k` data directories, and
   `ETCD_VERIFY` is off;
5. the trust-boundary contracts per member (`premises`), the context and client error classes, D22 (`hD22`, trusted
   text as a named hypothesis) and the class instances, all as authN's.

**What it does not say.** Liveness (a permitted call may fail: `Failed`); `Failed` skips the checks after it; a refusal
is any error; `KeepAlive` is not checked (D2); the members `3..k-1` serve and pass the barriers but no principal uses
them, and at `k ≤ 2` principals share members; with the examples' peers a permitted `TimeToLive` or `KeepAlive` at a
follower reports a live lease absent (not exercised; S7 serves the full peer handler); the lessor-side checks
(`TimeToLive`, `Leases`) are judged against the receiving member's lessor, which the driver's barrier brings past the
attach (a lagging member's verdicts: `nonissues/etcd-lease-checks-lagging-member.md`); the keys `TimeToLive` returns
are not claimed (the TOCTOU margin, `issues/etcd-lease-timetolive-keys-toctou.md`); no snapshot, restart, failure or
partition; a token is used only at the member that issued it; the simple token provider only.

**Compared with `etcd_authN_safe`.** Same start (`StartMembersAuth`), same member and principal mapping (0, `1 mod k`,
`2 mod k`), same premise shapes. New: `Hap`, `Hlp`, `Hlne`; the token; the ports; the result has no `WatchEnded`
(no watch). The cluster runs the revocable lease mode with auth on (authN: mode `none`). The workload is leases
instead of authkv's KV/watch rows.

**Compared with the lease theorems.** `etcd_leasegrant_safe`: one member, auth off, mode `mono`, `Hlp` and `Hlne`;
checks a grant is listed. `etcd_leaseexpiry_safe`: one member, auth off, mode `revocable` with expiry (no `Hlne`),
`Hlp`. `etcd_leasecatchup_safe`: three members, auth off, mode `mono`, `Hlp`, `Hlne`. `etcd_authlease_safe` is the
first closed theorem with the revocable mode on several members, with revocation by request, with leased puts, and
with leases at auth on; its lease premises are the union of theirs plus `leaseIdsApart`, which `cluster3.StartCluster`
already takes in the revocable mode.

## 3. Exported or frozen text that changes (old → new)

No closed theorem's statement changes (`etcd_auth_safe`, `etcd_auth3_safe`, `etcd_authN_safe`, the lease theorems:
proof bodies only, at lease mode `none` / the off contracts' `_false` laws).

| text | where | old | new | why |
|---|---|---|---|---|
| `etcdPutSpecOn`, `etcdPutSpecM` | client/v3 `KVServiceOn` (used by the exported `etcd_kv_auth_served_on`) | `⌜o.leaseID = W64 0⌝` | `etcdPutSpecOn`: no filter; `etcdPutSpecM on`: `⌜on = false → o.leaseID = W64 0⌝` | leased put at auth on (S3b's `putPermitOn` admits it) |
| `etcdTxnSpecOn` (and `etcdTxnSpecM`'s on part) | same | write branch `txn.txnPlain t` | S3b's leased-transaction form (`txnPlainL`, the permit's `txnPermitOn`) | leased put in a transaction |
| `kv.Put.spec` | `Spec/…/client/v3/kv__Put.lean` | `(putWireOf …).leaseID = W64 0` | dropped (the gRPC spec decides) | the client's leased put; a weaker premise, callers unaffected |
| `lessor.Grant/Revoke/TimeToLive/Leases.spec`, `retryLeaseClient.Lease*.spec` | `Spec/…/client/v3/` | over `isGrpcRpcs` (`GrpcSpec`) | over `isGrpcRpcsMd` (`GrpcSpecMd`), as `retryKVClient.Put.spec` already is | a user client's lease calls carry its token (C1) |
| **new** `isEtcdLeaseOn` and `client_lessor_isEtcdLeaseOn_served` | client/v3 `Results` | — | a `*lessor` of a user client meets: `Grant(ttl)` fires the caller's `Q id st` at the grant's commit (`leaseGrantResT`), `Revoke(id)` fires `Q st` at the revocation's (`leaseRevokeResT`), an error carries nothing | F3: linearizable lease specs |
| **new** `etcdLeaseTTLSpecOn`, `etcdLeaseLeasesSpecOn`, `etcd_lease_read_auth_served_on` | client/v3 `LeaseReadServed`/`AuthnServedOn` | — | `TimeToLive`/`Leases` served at metadata specs with auth on: a reply carries `leaseCheckFrom … (leaseKeysVerdictFrom … .read)` at lower bounds `n`, `m` (`checkLeaseTimeToLive`/`checkLeaseLeases`' posts) | the read handlers at auth on (D6: a sibling of `etcd_lease_auth_served_on`, which keeps its text) |
| C5′ pair: `lessorGrantOkG`, `lessorGrantOk`, `lessorRevokeOk`, `raftLessor` | v3rpc `InvLease` | the off contracts beside the `…M` ones | deleted; the seven client results (`etcd_leaseGrantHandlerOk`, `etcd_leaseRevokeHandlerOk`, `etcd_leaseMethodsOk`, `etcd_lease_served`, `etcd_kv_lease_served`, `client_lessor_isEtcdLease_served`, `client_new_isEtcdLeaseClient_served`) take `v3rpc.raftLessorM E.authOn s E ρ S` (one new binder `ρ`); v3rpc `lessorGrantOkL_server`, `lessorGrantOkLive_server`, `lessorRevokeOk_server` replaced by their `…M` versions (`lessorGrantOkLiveM_server`, `lessorRevokeOkM_server`, exported since S3c); the `pair` line of `etc/mode-allow.txt` deleted | D5 |
| `memberBootOn` | etcdstart `Defs` (API) | `(∃ m, lease.runCfg ρ.rd.kv.lm m) ∧ ρ.rd.kv.lg = false` | a lease-mode parameter `(lm : lease.Mode := .none)`: `ρ.rd.kv.lm = lm ∧ (∃ m, lease.runCfg lm m ∧ (m ≠ .none → lease.leasesNoExpiry))` | `NewServer.specM true` admits a granting cluster since S3c (`bootCfg`'s row) |
| `memberUpOn` | etcdstart `Defs` (API) | no lessor part | `+ srvLeaseRd s E m` (as `memberUp`), at the mode parameter | the read handlers' lessor |
| `StartMemberAuth.spec`, `StartMembersAuth.spec` | `Spec/…/etcdstart/` (API) | `memberPreOn` at `memberBootOn` (lease mode none) | `+ (lm : lease.Mode)`, `memberBootOn … lm`; post `memberUpOn … lm` | the auth start at the revocable mode |
| `allocNOn`, `alloc3On` | etcdstart `AllocNOn`/`Alloc3On` (API) | `γk.lg = false` | `+ lm`, `hrun : lease.runCfg lm lm`, `hap : lm = .revocable → leaseIdsApart ids`, as `allocN` | the cluster's names at the revocable mode |
| **new** per-member lessor law (§4.3) | server `Results` (exported) | — | `lessor_keys_of_read` | the lessor-side refusals at a follower |

Each changed definition keeps its old meaning at the old arguments (the default `lm := .none`; `on = false`), so
the off callers and the closed examples change in proof bodies only. `interface/` diffs: client/v3 (not an `etc/api`
package: reviewed here), etcdstart (`etc/api/etcdstart.txt`'s `Alloc3On`, `MembersAuthDefs`, `Defs`), v3rpc.

## 4. The Lean work

1. **Boot at the revocable mode with auth on** (etcdstart): `memberBootOn lm`, `memberBootOn_of`/`memberBootsOn_of`
   at `lm` (S3c's C6 already gives `srvClusterBootOn_alloc` the mode and prefixes), `allocNOn` with `hap`
   (`kvPfxOk_of_apart`, as `allocN`), `StartMemberAuth`'s proof at `NewServer.specM true` with `bootCfg_of_run`'s
   `hon` from `memberBootOn`'s new row, `memberUpOn`'s `srvLeaseRd`.
2. **The client's leased KV at auth on**: the three spec texts of §3; `etcd_kv_auth_served_on`'s proof over S3b's
   widened server specs (`EtcdServer.Put.spec` D3, `txnAppliedOk` D7); `kv.Put`/`txn.Commit` with `WithLease`
   (`withLeaseM`, `optSpec`).
3. **F3, the client's lease contract**: the lease client's specs at the metadata form; `isEtcdLeaseOn` and its
   served result over S3c's `etcdLeaseGrantSpecOn`/`etcdLeaseRevokeSpecOn` (the permit `leaseGrantPermitM` carries
   the caller's `kvOpStep (.leaseGrant id ttl)` update, S3a F3).
4. **The read handlers at auth on and the per-member lessor law (§4.3)**. `TimeToLive`/`Leases` served at metadata
   specs (`etcd_leaseTTLHandlerOk`'s at auth on: `checkLeaseTimeToLive`'s post through `LeaseServer`); `grpcUpOn`'s
   `grpcLeaseUp` already holds the four unary registrations (`v3rpc.leaseRegs`), so it is unchanged. The law: a
   linearizable read at member `j` (the barrier), answered after the entry that attached `k` to `id` committed, gives
   member `j`'s lessor `lease.lessorLb γl_j m` with, at every index `i ≥ m` that a reader can see while the client's
   model is at a log `L`, the lessor's snapshot the model's table at an applied prefix of `L` past the attach. With
   the driver's model (the main thread owns the client half and every step since the attach is its own: refused, or
   not touching `id`), this gives the probe's `leaseHoldsFrom γl_j m id k` for the window of the checks. The
   apply thread already keeps the auth-on table (`appliedTableM`, `srvRestM`); what is new is reading it at a
   member's lessor index from the read path's applied lower bound (auth3 A2's route (ii) for the auth store).
   **Probe** `Scratch/S4Probe.lean` (untracked, checked clean; copy `/shared/tmp/auth-lease-s4/S4Probe.lean`): `leaseKeysVerdict_refused`, a passed check refuted from that law's output
   and the auth state's denial.
5. **C5′ merge** (§3, D5).
6. **The driver**: `run`'s and `Main`'s specs and proofs (authN's skeleton: serve loop, set-up, barrier loop; then the
   sequential lease steps over the client's model with leases: `kvStateOf (kvModelOn …) (kvLeasesOn …)`, the grant,
   the attach, the refused steps leaving it, the revocation deleting the attached keys); `barriers`, `grantPut`,
   `noAuth`, `foreign`, `absent`, `reqCtx`, `refused` (each a small spec).
7. **Linking**: goose project `authlease` (`etc/goose.py`), `gen-init`, `MainLinked`, `Adequacy`, `Results`, the
   collection `etc/tcb-collections/authlease.txt`, interfaces, bounds, gates. No literal modes in the new package
   (`E.authOn` with `hon`, as authN mostly does; the mode gate's baselines are not to be raised).

## 5. Trusted text

**None new is expected.** The lease client and server calls the driver makes are proved code over existing axioms
(`EtcdServer.leaseTimeToLive`, `leasehttp`, `NewLessor`'s, unchanged; their auth-on adequacy is scope §7.2's). The
token is a Go-tested premise (`leaseIdsApart`), as `cluster3.StartCluster` takes it. If linking finds a premise of
an axiom the auth-on read path needs and cannot discharge (e.g. a `leaseTTLRow` reading at a follower), that is a
stop with the candidate axiom listed, a Go test and an axiom-skill review before it is added.

## 6. The token and the 15-bit question

`LeaseGrant` gives a grant without an ID `reqIDGen.Next() & (1<<63 - 1)`; the generator's bits 48–63 are the member
id's low 16 bits, so a lease id carries **15** bits of its member's id. Two members whose ids agree in their low 15
bits generate colliding lease ids (`issues/etcd-lease-id-mask-member-prefix.md`): a grant fails with "lease already
exists" or, after a revocation, silently reuses the id. The proof's revocable mode needs the granting members'
prefixes distinct after the mask (`kvPfxOk`, from `leaseIdsApart`, `idPfxsOf_mask_nodup`); `allocN` already takes
`hap : lm = .revocable → leaseIdsApart ids`.

**What it requires.** A member id is `sha1(peer URL ++ token)[0:8]`, so the ids of the first `k` members are a
prefix of the 1000's: one token whose 1000 ids are 15-bit distinct and 16-bit nonzero works for every `k`. 1000 ids
in 2^15 buckets collide with probability ≈ 1 − e^(−15.2); the search
(`/shared/tmp/auth-lease-s4/tokensearch/main.go`, etcd's `computeMemberID`) found **`authlease-3354335`** at the
ports 16000/17000 in ≈ 25 s on 24 threads (authN's `authN-1286` is 16-bit distinct only). `TestMemberIDs` checks it
with etcd's own code; `TestMainRun` checks that a lease granted through each member carries that member's 15 bits.

**Alternatives.** (a) Grants through member 0 only (scope §7.3's cheaper option): no `leaseIdsApart`, but a follower's
grant is not exercised, and `hap` would still be needed in a restricted form (`allocN` takes it for all members).
(b) A fork fix (the issue's branch: retry on a taken id): changes the verified code and the specs of `LeaseGrant`.
(c) Bound `k` lower: no gain, the token exists.

**Recommendation:** the token `authlease-3354335`, `leaseIdsApart ids` as a named premise `Hap` (beside `Hbf`,
not folded into a new `BootFacts`: the same premise text `cluster3.StartCluster` takes), grants through two members.

## 7. Work order and estimates (agent-days)

| # | item | days | stop |
|---|---|---|---|
| 0 | Draft (this), Go and tests | done | HARD STOP (statement) |
| 1 | build the worktree (the `.lake/build` is from 2026-11-13: a full build under the flock) | 0.5 | |
| 2 | §4.1 boot at the revocable mode with auth on (etcdstart) | 2–3 | |
| 3 | §4.5 C5′ merge | 1–2 | |
| 4 | Freeze package for §3's texts (2 review rounds) | 2–3 | HARD STOP (Freeze) |
| 5 | §4.2 leased KV at auth on (client) | 2–4 | |
| 6 | §4.3 F3 lease contract (client) | 3–4 | |
| 7 | §4.4 read handlers served at auth on + the per-member lessor law | 4–6 | |
| 8 | goose translation of `authlease`, `gen-init` | 0.5 | |
| 9 | §4.6 driver (`run`, `Main`, helpers) | 4–6 | HARD STOP (`Main.wp_proof` proved, before linking) |
| 10 | §4.7 linking, collection, interfaces, gates | 1–2 | HARD STOP (before `etc/land.sh`) |

Total **19–30 agent-days** (scope §7.4's 18–30 for the 3-member S4, less lease-mono3 step 2 and authN's start, which
are done, plus F3, the leased KV, the C5′ merge and the read handlers, which the scope did not count).

## 8. Risks

- **The per-member lessor law** (item 7) is the one new kind of server fact; its window ("while the client's model is
  at `L`") is what makes it true when `u` later revokes `Lu`. If the apply thread's lessor history is not tied to the
  applied table tightly enough (the table is the model's, the lessor's snapshots are the real lessor's), the law needs
  a new conjunct in `srvRestM` (an internal change, a form). Fallback: run the lessor-side checks at member 0 only
  after a barrier at member 0 (the single-member tie of scope §7.3), keeping the raft-path checks at every member.
- **First closed use of the revocable mode on several members** with request revocation: `kvGrantIds` across two
  granting prefixes, `kvPfxOk` from `hap`, the revocation's KV side (S3a session 6) at a follower's proposal. Each
  was proved in S3a–S3c, none was linked to a closed theorem.
- **The client's model with leases** (`kvStateOf … (kvLeasesOn …)`) has had no client: the driver is its first
  user; lemmas for "a revocation deletes exactly the attached keys" at the model may be missing (S3a's `revokeOn_after`
  is at the server).
- **Build cost**: the client's KV specs are imported widely (`etc/importers.py --count` before item 5); the full build
  takes the flock for hours.
- **Ports**: 16000–16999 and 17000–17999 are used by no example and lie below Linux's ephemeral range; the first
  choice (20000/21000) was taken by another session's `k8setcd3.test`. (Seen in passing: `restartN` and `authN` both
  use 29000/30000, so their tests cannot run at once.)
- **Mode gate**: the auth-on lease specs at the example level must use `E.authOn`, not `true`; a new package line in
  `etc/mode-baseline.txt` would be a raise.

## 9. Decisions needed

- **D1, the program** (§1): as written — authN's start, sequential lease workload, no authkv `Work`.
  **Recommend: yes.**
- **D2, `KeepAlive`**: leave it out of S4 (its auth-on stream serving and the client's `KeepAliveOnce` spec are a
  separate piece, ≈ 3–5 days; the Go test shows the refusal at every member), as a follow-up with S7.
  **Recommend: out.**
- **D3, the token and premise** (§6): `authlease-3354335`, `Hap : leaseIdsApart ids` named. **Recommend: yes.**
- **D4, two granting members** (0 and `1 mod k`) rather than member 0 only. **Recommend: two.**
- **D5, the C5′ merge form**: the seven client results at `raftLessorM E.authOn s E ρ S` (no literal mode; one new
  binder each) and the four off contracts deleted, vs keeping the pair (no change, cleanup later).
  **Recommend: merge as stated** (the stage was asked to).
- **D6, the read handlers' served result**: a sibling `etcd_lease_read_auth_served_on`, vs widening
  `etcd_lease_auth_served_on` to four methods (its statement changes). **Recommend: the sibling.**
- **D7, the KV specs' filters**: drop in place (`etcdPutSpecOn`, `etcdPutSpecM`'s on part, `etcdTxnSpecOn`), vs new
  `…L` specs beside them (a twin, the mode gate's `twin` count). **Recommend: in place.**
- **D8, `memberBootOn`'s lease row**: `ρ.rd.kv.lm = lm ∧ ∃ m, lease.runCfg lm m ∧ (m ≠ .none → leasesNoExpiry)`, the
  premise `leasesNoExpiry` carried by the boot bundle (from the closed theorem's `Hlne`), vs a premise of
  `StartMemberAuth.spec`. **Recommend: in the bundle** (as `memberBoot`'s `runCfg`).
- **D9, the result values**: `Ok`/`Failed` only (no watch, no `WatchEnded`). **Recommend: yes.**

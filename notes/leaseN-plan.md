# leaseN: the lease rows of Figure 2 for k members (plan, 2026-11-16)

For etcd-grove-02 and the user. Branch `leaseN` (worktree `/shared/etcd-grove-leaseN`, off lean `5d2a12df97`).
The goal (the user's, 2026-11-15/16): every theorem of the paper's Figure 2 is about `k` members, `1 ≤ k ≤ 1000`,
on the generic start (`etcdstart.Members`/`StartMembers`), as putgetN, txnlinfaultsN, restartN, authN and kvN are.
This stage: `etcd_lease_safe` and `etcd_leaseexpiry_safe`; and whether `etcd_leasegrant_safe` and
`etcd_leasecatchup_safe` fold in.

**Status (2026-11-16):** the statements (§2) APPROVED by the user, 2026-11-16, via etcd-grove-02, as drafted;
D1-D12 (§8) decided by etcd-grove-02 as recommended (D9: leasegrantN deferred; D10: leasecatchupN queued next).
Lean work in §6's order, leaseN first (it may land on its own).

## 0. Summary

- **Two programs, N versions beside the one-member ones** (as putgetN/authN; replace-in-place was the user's choice
  for k8s only): `examples/etcd/leaseN` (`etcd_leaseN_safe`) and `examples/etcd/leaseexpiryN`
  (`etcd_leaseexpiryN_safe`). The one-member theorems keep their text.
- **leaseN**: `k` members, every member serves gRPC; at every member, through its own client, the lease example's
  two reads and checks (no lease listed twice; `TimeToLive` answers about the lease asked). Lease mode `none` (no
  grants), as `etcd_lease_safe`. New premises over putgetN's: only `leasePeersOk` (the one-member theorem's).
- **leaseexpiryN**: a lease of the minimum TTL granted through every member; at every member, its listing polled
  until it no longer lists the lease granted through it, then listed again: panic if listed again ("an expired lease
  is no longer listed", the Figure 2 row's words). **"Gone" is read off the member's listing, not off `TimeToLive`**:
  the one-member example's TTL-then-listing check is false through a follower (§1.3, Go test), and the TTL axiom's
  content is a single-member row anyway. Revocable mode; new premises over putgetN's: `leaseIdsApart ids` (the
  15-bit premise, with a searched token) and `leasePeersOk`.
- **Trusted text: none.** **Exported/frozen text that changes: none** (new theorems only).
- **leasegrant** (not a Figure 2 row): does not fold into either (its "listed" check needs no expiry, mode `mono`);
  a `leasegrantN` port is 2-3 days if wanted (D9). **leasecatchup** (a Figure 2 row, 3 members): not a fold either;
  a `leasecatchupN` port on txnlinfaultsN's k-member start, a stage of its own after this one (D10).
- **Estimate** 7-11 agent-days for both theorems (§6).

## 1. The Go programs and their tests

Both use the generic start unchanged (`etcdstart.Members`, `StartMembers` with `NoSnapCount`/`NoSnapCatchUp`, auth
off), serve every member (`etcdstart.Serve` in a loop, authN's pattern) and connect one client per member
(`etcdstart.NewClient`). `Main(k uint64)` has no result (as the one-member `Main()`); the body is a `run(srvs, ms,
lg) int` (`Checked`/`Failed`, the result ignored by `Main`, leasecatchup's pattern) so that a test can tell a checked
run from an early return. `k = 0` needs no special case (the loops are empty). No `holdToken` goroutine (the one-member
examples' is unused since per-type stage B3: gRPC runs borrow from the server's run pools).

### 1.1 leaseN (`examples/etcd/leaseN/leaseN.go`)

`Main(k)`: `ms := Members("leaseN", k, 10000, 11000)` (member `i` is `leaseN-i`, peer `127.0.0.1:(10000+i)`, client
`127.0.0.1:(11000+i)`); `StartMembers(ms, "leaseN-2422", …)`; `run`: serve loop; then for each member, `check(addr)`:
`NewClient`, `Leases()` (panic if an id is listed twice), `TimeToLive(7)` (panic unless the answer's `ID` is 7).
Token `leaseN-2422`: the first `leaseN-<n>` whose first 1000 members' ids have distinct nonzero 16 low bits (16 bits
suffice: no member grants a lease).

At a follower, `TimeToLive` forwards to the leader's peer URL (`leasehttp.TimeToLiveHTTP`), which the examples' peer
listeners answer 404 (raft handler only), read as "not found": the answer is `TTL = -1` about the asked id. So the
follower path of `EtcdServer.leaseTimeToLive`'s ID claim, which `etcd_lease_safe` never runs (one member is always
its own leader), is exercised at every `k ≥ 2`.

### 1.2 leaseexpiryN (`examples/etcd/leaseexpiryN/leaseexpiryN.go`)

`Main(k)`: `ms := Members("leaseexpiryN", k, 12000, 13000)`; `StartMembers(ms, "leaseexpiryN-1973196", …)`;
`run`: serve loop; for each member `j`: `NewClient`, `Grant(1)` (TTL raised to the minimum, 2 s), keep `clis[j]`,
`ids[j]`; then for each member `j`: `gone(clis[j], ids[j])` (up to 80 listings 250 ms apart until `ids[j]` is not
listed; `Failed` if never or on an error), then one more `Leases()`: **panic if it lists `ids[j]`**.

Why each member checks the lease granted through it: the member that proposed a grant applied it before answering
(the grant's spec gives `leaseLiveFrom` at that member's lessor), so its listing reads a lessor that held the lease;
a listing without it is at an index past the grant, and an id is granted once (`lessorAt_absent_stays`), so the next
listing (at a later index of the same lessor) cannot have it. A member that did not grant the lease may not have
applied the grant yet: its "not listed" would say nothing (D5).

Token `leaseexpiryN-1973196`: the first `leaseexpiryN-<n>` whose first 1000 members' ids have distinct nonzero 16 low
bits **and distinct 15 low bits** (`leaseIdsApart`: a lease id carries bits 0-14 of its member's id in bits 48-62,
`issues/etcd-lease-id-mask-member-prefix.md`; two granting members agreeing there can generate the same lease id, and
after a revocation a reused id would be listed "again"). Found in 29 s on 24 threads
(`/shared/tmp/leaseN/tokensearch/main.go`, S4's search with the bit count a parameter; it reproduces
`putgetN-1405` and `authN-1286`).

### 1.3 Why not the one-member check (`TestTTLThroughFollowerPanics`)

The one-member example polls `TimeToLive` until `TTL = -1 ∧ GrantedTTL = 0`, then panics if `Leases()` lists the
lease. On 3 members started as Main starts them, a lease granted through a follower is live (the follower lists it),
yet the follower's `TimeToLive` answers not found on the first poll (the leader's 404): the one-member `Main`, run
through that follower, panics. The test passes (the behavior is there) on every run. This is the deployment the
existing trust-boundary spec already describes (`EtcdServer.leaseTimeToLive.spec`: "answers 404, which
`TimeToLiveHTTP` reads as `ErrLeaseNotFound`: an error the triple allows, though the lease may exist", and its
content only under `leaseTTLRow`, "`s` is its cluster's only member"), not a new finding. With etcd's full peer
handler the check would still be false through a lagging follower (the leader revoked and answered, the follower
not yet applied: `LeaseLeases` reads the local lessor, `v3_server.go:737`), already recorded in the lagging-member
family (`nonissues/etcd-lease-checks-lagging-member.md`, `issues/etcd-lease-renew-keys-follower-lag.md`).

### 1.4 Ports

- leaseN: peers 10000-10999, clients 11000-11999.
- leaseexpiryN: peers 12000-12999, clients 13000-13999; its tests' own clusters (≤ 7 members) 14000-14006,
  14100-14106 (`TestTTLThroughFollowerPanics`), 14200-14206, 14300-14306 (`TestRunChecked`).

No example, in lean or in any worktree under `/shared/etcd-grove*`, uses 10000-15999 (checked by grep: the ranges in
use are 16000/17000 authlease, 20000/21000/22000, 23xxx one-member examples, 24000/25000 putgetN, 26000-28000
txnlinfaultsN, 29000/30000 authN and restartN, 33xxx, 40xxx, 45xxx, 65xxx). All lie below the ephemeral range
(32768-60999).

### 1.5 Tests (`GOWORK=off`, `PATH=/usr/local/go/bin:$HOME/go/bin:$PATH`, `systemd-run --scope -q -p MemoryMax=32G`)

- `TestMemberIDs` (both): for every `k ≤ 1000`, the ids etcd computes (`membership.NewClusterFromURLsMap`) have
  distinct nonzero 16 low bits; leaseexpiryN also distinct 15 low bits.
- `TestMembers` (both): names and addresses at `k = 3`; `Main(0)` returns.
- `TestMainRun` (both): `Main(k)` for real, `k` drawn from {1, 2, 3, 5, 7} (`LEASEN_MEMBERS`,
  `LEASEEXPIRYN_MEMBERS` override; logged first). Then from outside, at every member: it answers (Main served it),
  `MemberList` has `k` members; leaseN: one leader, empty listing, `TimeToLive(7)` not found about 7; leaseexpiryN:
  empty listing at every member (every lease expired everywhere), and a lease granted now through each member has
  bits 48-62 equal to that member id's 15 low bits.
- `TestRunChecked` (leaseexpiryN): `run` on a cluster of its own returns `Checked` (the polls do not time out, so
  the panic check is reached, not skipped).
- `TestTTLThroughFollowerPanics` (leaseexpiryN): §1.3.

**Results** (`/shared/tmp/leaseN/runs.log`; etcd at the examples' `go.mod` pin `6e8f0c004c15`): all pass, no
failure. Per package: two rounds of every test at `k ∈ {1, 2, 3, 5, 7, 9}` (12 runs each), 4 runs at a random `k`, and
one run each at `k = 3` and `k = 15` after the last test edit: 18 runs of each package. leaseN's `Main` takes 1-4 s;
leaseexpiryN's 2.7-13 s (`run` 3-6 s at every `k` up to 15: one expiry wait, the members polled in turn).
`TestTTLThroughFollowerPanics` saw the not-found answer for a live lease through a follower on every run. Nothing
that looks like an etcd bug.

## 2. The closed statements (HARD STOP)

Shared shape: putgetN's (`etcd_putgetN_safe`), at the new program; `ids`, `ps`, `ctxs`, `boot` and
`etcd_putgetN.BootFacts` as putgetN's and authN's; `premises` putgetN's per-member `bootPremise` at the package's
token and `dirN`, `bootMarshal`, `commonPremises`; the addresses are the `2k` peer and client addresses (every member
serves gRPC, authN's `authNAddrs`), the directories `k` `<name>.etcd`, the names the read package's two metric names.
The ghost-state bundle is a form decided at linking (putgetN's `putgetNGF` if it carries the lessor's functors, else
one of the package's, as `leasekvGF`/`leaseexpiryGF`).

### 2.1 `etcd_leaseN_safe`

```lean
theorem etcd_leaseN_safe [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.leaseN.Assumptions]
    [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]
    [go_etcd_io.etcd.client.v3.DialWithBalancerBody] [log.NewModel]
    (Hctx : ∀ hG, ContextReadErrs (hG := heapAt hG lctx))
    (Hcec : ∀ hG, ContextErrsClient (hG := heapAt hG lctx))
    (k : Nat) (hk1 : 1 ≤ k) (hk : k ≤ 1000)
    (ids ps : List w64) (ctxs : List (List w8)) (boot : List LogEntry)
    (Hlen : ids.length = k) (Hbf : etcd_putgetN.BootFacts ids ps ctxs boot)
    (Haf : authRecordsFit) (Hbuq : apply.backendUnderQuota) (Hrf : grpcRepliesFit)
    (Hdbo : storage.diskOk)
    -- as etcd_lease_safe: whatever serves /leases/internal at a peer URL answers 200 only as etcd's
    -- lease handler does (the examples' peers answer 404)
    (Hlp : leasePeersOk)
    (HNs : prometheus.namesUnclaimed (leaseNProgram k) leaseNNames)
    (HAs : addrsUnclaimed (leaseNProgram k) (etcd_leaseN.leaseNAddrs k))
    (HDs : dataDirsAbsent (leaseNProgram k) (etcd_leaseN.leaseNDirs k))
    (HEnv : verifyEnvOff (leaseNProgram k))
    (n : Nat)
    (Hprem : ∀ hG, ⊢ etcd_leaseN.premises (hG := heapAt hG lctx) k n ids ps ctxs boot)
    (σ : state) (g : GlobalState) (Hlctx : σ.goState.goLctx = lctx) (Hinit : IsInit σ)
    (Hthreads : σ.threads = 1)
    (κs : List Observation) (t2 : List Expr) (σ2 : CfgState)
    (Hsteps : RealNsteps n ([leaseNProgram k], ((σ, g) : CfgState)) κs (t2, σ2))
    (Hn : n + 2 ≤ 2 ^ 28) :
    (∀ v t2', t2 = Val v :: t2' → v = #()) ∧
    (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
    (∀ v, Val v ∈ t2 → v.isPanic = false)
```

`leaseNProgram k := leaseN.initialize' #() ;; Main #(W64 k)`; `leaseNAddrs k` the members' peer addresses then
their client addresses; `leaseNDirs k` the `leaseN-i.etcd`.

**In plain words.** For every member count `k` from 1 to 1000: run the program from a fresh state with one thread
for any number `n` of steps (`n + 2 ≤ 2^28`). Then the main thread, if finished, returned; no thread is stuck; no
thread panicked. Not panicking means: at every member, through a client of that member, a listing of the leases that
answered listed no lease twice, and a `TimeToLive(7)` that answered was about lease 7 (also at a follower, which asks
the leader). This holds if:

1. etcd's member ids for the `k` members, the peers in `bootstrap`'s order, their contexts and the boot log are what
   Go computes; the ids' 16 low bits are distinct and not 0 (`BootFacts`, putgetN's; `TestMemberIDs` checks it for
   every `k ≤ 1000` at the token `leaseN-2422`);
2. the size facts putgetN assumes (auth records fit, the backend under quota, gRPC replies fit, the disk behaves);
3. a peer answers `/leases/internal` with 200 only as etcd's lease handler does (`leasePeersOk`, `etcd_lease_safe`'s;
   true of the examples' peers, which answer 404);
4. at start nothing else claims the program's metric names, its `2k` addresses or its `k` data directories, and
   `ETCD_VERIFY` is off;
5. the trust-boundary contracts per member (`premises`), the context and client error classes and the class
   instances, as putgetN's.

**Compared with `etcd_lease_safe`:** `k` members on the generic start instead of `StartServer`; every member serves
and is checked; premises putgetN's list forms plus the one-member theorem's `Hlp`; no new kind of premise.

### 2.2 `etcd_leaseexpiryN_safe`

As §2.1, at `leaseexpiryNProgram k`, `leaseexpiryNNames`, `etcd_leaseexpiryN.leaseexpiryNAddrs k`,
`etcd_leaseexpiryN.leaseexpiryNDirs k`, `etcd_leaseexpiryN.premises` (token `leaseexpiryN-1973196`), with one more
premise beside `Hbf`:

```lean
    (Hlen : ids.length = k) (Hbf : etcd_putgetN.BootFacts ids ps ctxs boot)
    -- NEW: the members' ids 15-bit distinct (allocN's `hap` at the revocable mode; TestMemberIDs)
    (Hap : leaseIdsApart ids)
    ...
    (Hlp : leasePeersOk)
```

(no `lease.leasesNoExpiry`: the leases expire, as in `etcd_leaseexpiry_safe`). Result `#()`, no stuck thread, no
panic.

**In plain words.** For every member count `k` from 1 to 1000, as above; not panicking means: at every member, once
a listing of that member's leases (through a client of that member) did not list the lease granted through that
member, its next listing did not list it either: an expired lease is no longer listed, at every member. Nothing is
said about time: whether, or when, a lease expires (a member whose listing still has it after the polls ends the run
without the check). The hypotheses are §2.1's 1-5, plus:

6. **the members' ids' 15 low bits are distinct** (`leaseIdsApart ids`, `E/SrvRaftLog.lean:536`, the premise
   `cluster3.StartCluster` and `allocN` take in the revocable mode and auth-lease S4's `etcd_authlease_safe` takes;
   `TestMemberIDs` checks it for every `k ≤ 1000` at the token `leaseexpiryN-1973196`).

**Compared with `etcd_leaseexpiry_safe`:** `k` members; every member grants and checks; the check's "gone" is a
listing without the lease instead of a `TimeToLive` not found (§1.3); the new premise `Hap`; `Hlp` kept (the lease
service's registration takes it, though no `TimeToLive` is called: dropping it needs a Leases-only served lemma,
not worth it).

## 3. Exported or frozen text that changes

None. No closed theorem's statement changes; `etcd_lease_safe` and `etcd_leaseexpiry_safe` stay. New exported text:
the two closed theorems, their `Main` results (`leaseN_Main`, `leaseexpiryN_Main`), the packages' `Defs`/`Dir`
(`premises`, addresses, directories), `etc/tcb-collections/leaseN.txt` and `leaseexpiryN.txt`. No `etc/api` package
changes (the examples import etcdstart's existing importable modules: `MembersDefs`, `AllocN`, `AdequacyMembers`,
`Served`, `ServedLease`, the specs).

## 4. Trusted text

None new. The axioms the theorems rest on are the one-member lease theorems' and putgetN's (expected: the union of
`etc/tcb-collections/lease.txt`/`leaseexpiry.txt` and `putgetN.txt`; checked at linking). leaseN is the first closed
theorem that runs the follower half of `EtcdServer.leaseTimeToLive`'s `ID` claim (an existing axiom, reviewed
2026-11-02, `notes/axiom-review/lease-ttl-id.md`; the Go tests above run it at every `k ≥ 2`). leaseexpiryN does not
call `TimeToLive`.

## 5. The Lean work

1. **Translation**: Goose projects `leaseN`, `leaseexpiryN` in `etc/goose.py` (as `putgetN`); `etc/gen-init.py`
   (`Init`, `PkgTable`).
2. **leaseN**: `Base`, `Defs` (`members`, `token`, `startOf` with every client address, `premises`), `Dir` (authN's
   `Dir.lean` at the new prefix and bases: names, peers and clients distinct, literals, ports, addresses and
   directories); specs and proofs of `check` (the one-member `Main`'s body after `Serve`: `NewClient`, `Leases` with
   the duplicate loop, `TimeToLive`, over `client.etcdLeaseReadAt addr`), `run` (serve loop at mode `none` with
   `kv_lease_served` per member, then the check loop), `Main` (`allocN` at `.none`, `StartMembers`).
3. **leaseexpiryN**: the same skeleton; `allocN` at `.revocable` with `hap := Hap` and
   `lease.runCfg_revocable (srvRevokeLevels_of_srvLevels Hlev) hrev`; `memberUp`'s `srvLeaseRd s E .revocable` per
   member; the serve loop with `kv_lease_served … .revocable` (each member's `etcdLeaseGrantLiveAt`); the grant loop
   (its invariant: per granted member, `leaseLiveFrom (mvccLeases E_j.γ) i_j id_j` and `lessorLb`, a `[∗list]` over
   the members so far, the clients' slices); the check loop with the nested `gone` loop (the one-member `Main`'s poll
   loop with `Leases` in place of `TimeToLive`: `leaseIdsAt` at `j ≥ lb`, not listed gives `leaseAbsentFrom`) and the
   final listing (`lessorAt_absent_stays`, verbatim from the one-member proof).
4. **Linking** (each): `MainLinked` (with `srvRevokeOpen_intro EtcdServer.wp_revokeExpiredLeases` for leaseexpiryN,
   as the one-member one), `Adequacy` over `etcd_adequate_members`, `Results`, the collection, gates.

## 6. Work order and estimates (agent-days)

| # | item | days | stop |
|---|---|---|---|
| 0 | this plan, Go and tests | done | **HARD STOP (statements)** |
| 1 | build the worktree (targeted: putgetN's, authN's and the lease examples' imports) | 0.5 | |
| 2 | translation, gen-init (both) | 0.5 | |
| 3 | leaseN: Defs/Dir, `check`, `run`, `Main` | 2-3 | checkpoint (`Main.wp_proof` proved) |
| 4 | leaseN linking, collection, gates | 0.5-1 | HARD STOP (before `etc/land.sh`) |
| 5 | leaseexpiryN: Defs/Dir, allocN at revocable, serve/grant/check loops, `Main` | 3-5 | checkpoint (`Main.wp_proof` proved) |
| 6 | leaseexpiryN linking, collection, gates | 0.5-1 | HARD STOP (before `etc/land.sh`) |

Total **7-11 agent-days**. leaseN can land on its own before leaseexpiryN.

## 7. Risks

- **First closed use of `allocN`/`StartMembers` at the revocable mode** (putgetN, txnlinfaultsN, restartN start at
  `.none`; lease-mono3 step 2 proved `alloc3`/`cluster3.StartCluster` at `.revocable` with `leaseIdsApart`, and
  `allocN` takes `hap` the same way, unused so far). If a piece of the revocable boot is missing in `allocN`'s proof,
  it is an internal fix in etcdstart (a form). auth-lease S4 is taking the same route with auth on (`allocNOnM`).
- **Expiry on several members**: the leader's lessor revokes through raft (`revokeExpiredLeases`, proved, generic in
  the membership as far as read); followers' lessors are demoted and only apply. No single-member assumption was seen
  outside `leaseTTLRow` (which leaseexpiryN does not use); if one turns up, it is a stop.
- **auth-lease S4 overlap** (`/shared/etcd-grove-rs56`): S4 moves the client lease library's specs
  (`lessor.Grant/TimeToLive/Leases.spec`) to the metadata form (`isGrpcRpcsMd`) and merges the C5′ lease contracts
  (`raftLessor` → `raftLessorM`), changing the one-member lease examples' proof bodies. leaseN/leaseexpiryN call the
  same client methods and `kv_lease_served`: whichever lands second adapts its proof bodies (no statement changes).
  I change no module S4 changes (D11).
- **Loop invariants with per-member lease facts** (leaseexpiryN's grant loop carries `k` clients and `k` lease
  facts): the pattern is authN's barrier loop plus the one-member proof's facts; moderate.
- **Bounds and mode gates**: new loops over `StartMembers`'s results may count like authN's (+13 bounds, mode-allow
  entries); a raise needs the coordinator's decision.
- **Ports** are fixed (§1.4); the gates' fixed-port tests (k8s 2404x) do not overlap.

## 8. Decisions needed

- **D1, N versions beside** the one-member theorems, named `etcd_leaseN_safe` and `etcd_leaseexpiryN_safe`
  (packages `leaseN`, `leaseexpiryN`). **Recommend: yes** (the user's default; Figure 2 would cite the N rows).
- **D2, leaseN's reads at every member** (each through its own client), vs member 0 only. **Recommend: every
  member** (otherwise `k` adds nothing to the theorem; every member exercises the follower path of `TimeToLive`).
- **D3, leaseN's lease mode `none`** (no grants: the checks hold whatever the lessors hold, as `etcd_lease_safe`),
  vs grants through the members. **Recommend: `none`** (a faithful port, no 15-bit premise; grants are leaseexpiryN's).
- **D4, leaseexpiryN reads "gone" off the member's own listing**, not off `TimeToLive` (§1.3: the one-member check is
  false through a follower). Alternative: serve etcd's lease handler on the peers, a new trusted contract for the
  forwarded `TimeToLive`, a barrier, and a per-member lessor law (S4's item 7): trusted text and S4-sized risk.
  **Recommend: the listing.**
- **D5, leaseexpiryN's grants through every member, each member checking its own lease**, vs grants through member 0
  only with every member checking it (then a member must first see the lease listed: an extra poll; and `allocN`
  still takes `leaseIdsApart` at the revocable mode). **Recommend: every member.**
- **D6, the 15-bit premise and token**: `Hap : leaseIdsApart ids` named beside `Hbf` (S4's form), token
  `leaseexpiryN-1973196`. **Recommend: yes.**
- **D7, `Main(k)` without a result** (as the one-member `Main()`), `run` returning a status `Main` ignores, vs
  `Main(k) int`. **Recommend: as written** (the theorems keep the one-member result `#()`).
- **D8, ports** §1.4. **Recommend: yes.**
- **D9, leasegrant** (not a Figure 2 row): no natural fold (its "the grant is listed" needs no expiry: mode `mono`
  with `leasesNoExpiry`, where leaseexpiryN's leases expire). A `leasegrantN` (grant through every member, each lists
  its grant) on leaseN's skeleton is 2-3 days. **Recommend: not now**; offer after leaseN lands.
- **D10, leasecatchup** (a Figure 2 row, 3 members): not a fold (it cuts and mends peers and needs snapshots). A
  `leasecatchupN` on txnlinfaultsN's k-member start (snapshot settings, `cluster3.PeerStep` already by index): the
  lease granted through member `k-1`, that member cut from every other, fillers through member 0, mended, its
  listing polled; mode `mono`, no 15-bit premise; at `k ≤ 2` the fillers cannot commit while a member is cut, so the
  run ends without the check. 4-6 days. **Recommend: a stage of its own right after this one** (needed for the
  goal: every Figure 2 row at `k` members).
- **D11, the `Dir` vocabulary**: copied per package from authN's `Dir.lean` (as authN did from putgetN's), vs a
  generic `etcdstart` module (an API addition). **Recommend: copy now**; a generic module is a later cleanup.
- **D12, sequencing with S4**: proceed on lean now; whichever of S4 and leaseN lands second adapts the lease client
  calls' proof bodies. **Recommend: yes**; the coordinator may prefer leaseexpiryN's client-call proofs after S4's
  client spec change lands (item 6) to avoid doing them twice.

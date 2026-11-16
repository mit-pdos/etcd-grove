# Clusters of any size: Scope for `etcd_putgetN_safe` (2026-11-15, for etcd-grove-81; notes and scratch probes only)

**The user's goal (2026-11-15).** The next multi-member theorems should not be tied to 3 members. They should cover
the common deployments, clusters of 3, 5 and 7 members. The goal is one theorem over all odd member counts;
restricting to odd counts is fine. Start with the easiest safety theorem to learn how hard this is.

**Short answer.**
- One theorem `etcd_putgetN_safe`, quantified over the member count `k` with `1 ≤ k ≤ 1000`, is feasible.
  Raft, the server and the cluster allocation are already generic in the voter list.
  Everything that names three members lives in the examples' code (`examples/lib/{etcdstart,cluster3}`,
  the examples' `Defs`/`Main`/`Adequacy`).
- No step needs `k` to be odd. Even `k` works in etcd and in the proof, so the recommended theorem holds for every
  `1 ≤ k ≤ 1000`. That covers 3, 5 and 7 and is strictly stronger than a statement for odd `k` only (§1).
- **Estimate for putgetN:** 7-12 agent-days, about 2-2.5 weeks of calendar time with reviews.
  The riskiest remaining piece is the Go loop that starts the `k` members, together with its loop invariant (§5, §6).
- The scratch probes are sorry-free. They cover the generic cluster allocation (`allocN`'s three pieces) and
  "a generated address is a loopback literal" (§5).
- **Putget is the right experiment, not lease3** (§0).

Abbreviations:
- `X/` = `Proof/github_com/mit_pdos/etcd_grove/examples/`;
- `XS/` = `Spec/github_com/mit_pdos/etcd_grove/examples/`;
- `E/` = `Proof/go_etcd_io/etcd/server/v3/etcdserver/`.

Line numbers are at lean `7d9d727fba`.

---

## 0. Which theorem to experiment on: putget, not lease3

Putget is the right first target:
- `etcd_putget3_safe` exists. Its whole three-member apparatus is the thing to generalize: `alloc3`, three
  `StartMember` calls, `BootFacts id₁ id₂ id₃`, `dir3`, `initURLs3`.
- Its workload (one Put, one Get through member 1) does not depend on the cluster size. The experiment therefore
  measures only the cost of generality.
- A 3-member `etcd_lease_safe` does not exist yet. Doing it first would mix two experiments: lease reads on a
  cluster, and N members. It also brings the lease mode's extra premises (`lease.runCfg`, `leaseIdsApart`,
  `leasePeersOk`).

`allocN` will carry the lease-mode arguments anyway, as `alloc3` does (`hap : lm = .revocable → leaseIdsApart ps`
is already over a list). Once putgetN exists, a leaseN theorem is a port, not a new design.

## 1. The statement

### Shape

`Main` takes the member count as an argument: `func Main(k uint64)`. The program is
`putgetN.initialize' #() ;; Main #(W64 k)`. The closed theorem quantifies over `k`:

```lean
theorem etcd_putgetN_safe … (k : Nat) (hk1 : 1 ≤ k) (hk : k ≤ 1000)
    (ids : List w64) (ps : List w64) (ctxs : List (List w8)) (boot : List LogEntry)
    (Hlen : ids.length = k) (Hbf : etcd_putgetN.BootFacts ids ps ctxs boot)
    … (HAs : addrsUnclaimed (putgetNProgram k) (putgetNAddrs k))
    (HDs : dataDirsAbsent (putgetNProgram k) (putgetNDirs k)) (HEnv : verifyEnvOff (putgetNProgram k))
    (n : Nat) (Hprem : ∀ hG, ⊢ etcd_putgetN.premises k n ids ps ctxs boot) …
    (Hsteps : RealNsteps n ([putgetNProgram k], …) κs (t2, σ2)) (Hn : n + 2 ≤ 2 ^ 28) : …
```

In this statement:
- `n` stays the execution's step count, as in every closed theorem. The member count is `k`.
- `ids` lists the member ids in member order. Member `i` is named `putgetN-i`, has peer address
  `127.0.0.1:(24000+i)` and client address `127.0.0.1:(25000+i)`. Only member 0's client address is served.
- `BootFacts ids ps ctxs boot` is `BootCore ps ctxs boot ∧ ps.Perm ids`. This is putget3's `BootFacts` with the
  three ids replaced by a list. `BootCore` is already over a list (`E/SrvRaftLog.lean:515`).
- `premises` holds the contract `bootPremise` for each `i < k`, as a `[∗list]` over `List.range k`,
  plus `bootMarshal` and `commonPremises`, as today.

### What Goose and the adequacy theorem allow

- **Goose.** A `Main` with a `uint64` parameter is an ordinary function. `etcd_adequate_members`
  (`X/lib/etcdstart/AdequacyMembers.lean:46`) takes any `body : Expr`. It also already takes the members' start
  bundles as a list `ms`.
- **Names and addresses.** They are built with `strconv.FormatUint(uint64(i), 10)` rather than `Itoa`, so that the
  Lean side is `decStr`, which has `decStr_inj` (`Proof/strconv/FormatUintDefs.lean:94`). `FormatUint` is already a
  trust-boundary spec (`Spec/strconv/FormatUint.lean`), so the trust base gains nothing.
- **Thread budget.** `Hn : n + 2 ≤ 2^28`, `threadBound = max (n+2) srvLevelK` and `srvLevels` do not depend on `k`:
  - A fork takes its token from the thread fuel (`Perennial/GooseLang/Threads.lean`, header), not from `Main`'s token.
  - `StartMember` hands the main thread's token back in its post (`srvGoRes`, `X/etcd/putget3/Main.lean:286`).
    A loop can therefore thread it through `k` iterations.
  - The `srvLevels` levels are per thread.
- **Per-member budgets.** `receiptBound ≤ N+1` and `N + 7 + bootWB ≤ backend.wbInit` are per member and are
  unchanged.
- **Where `k` is bounded.** Only two places bound `k`:
  - `netAddrLit` requires ports `≤ 65535` (`Proof/net/InvNet.lean:84`). With the port scheme above, that is
    `k ≤ 1000`, which also keeps the peer and client ranges disjoint. Any fixed bound works; 1000 is a choice
    (decision Q3).
  - `idPfxsOf_ok` derives `ps.length ≤ 2^16 - 1` from `BootCore`'s 16-bit distinctness (`Proof/go_etcd_io/etcd/pkg/v3/idutil/Defs.lean:241`).
- **`BootCore` is a hypothesis about the ids Go computes.** The ids are etcd's SHA-1 of the peer URLs and the token,
  and Lean never computes them; it only receives them through `bootstrapContract`. `BootCore` requires their 16 low
  bits to be distinct and nonzero. That holds for a given `k` only if etcd's ids happen to avoid a collision. The
  probability of a collision is about `k²/2^17`: about 0.03% at `k = 7`, about 2% at `k = 50`.
  - For a `k` where the ids collide, the theorem is vacuous at that `k`, but still true.
  - The Go `TestMemberIDs` checks the hypothesis concretely for the counts we claim (§4). This is the same
    discipline as today's per-configuration `TestMemberIDs`.

### Odd or even

**Nothing in the proof needs odd `k`, and even `k` works in etcd.**
- **etcd.** A cluster of 2 or 4 members commits with a majority of `k/2 + 1`. That is safe, only less fault-tolerant
  than `k - 1` members. etcd's documentation recommends odd sizes for availability, not for safety.
- **Raft.** The proof is generic in the voter set:
  - `quorum`'s `MajorityConfig`/`JointConfig` specs are over any configuration.
  - No raft or server file mentions a parity, or a list of length 3.
  - The one-voter path (`k = 1`), the read-index shortcut, is in the pinned code and covered (putget's
    `etcd_putget_safe` already runs it).
- **Server.** `srvClusterBoot_alloc` takes any `ps` with `ps.Nodup`, `ps ≠ []` and `0 ∉ ps`
  (`E/NewServerAlloc.lean:151`).

So the recommended statement is `1 ≤ k ≤ 1000`. A `k % 2 = 1` premise would only weaken it (decision Q1).

### The cheapest route to exactly 3, 5 and 7 (the fallback)

The fallback is three programs, `putget5` and `putget7` (and putget3 redone), each with a Go constant `k`. Each
calls the same generic library: `etcdstart.StartMembers` over a slice, and `allocN`.

Each program needs:
- its own thin `Main` proof;
- `Adequacy`, `MainLinked`, `Results`, `PkgTable` and `Init`;
- `decide` for its address and directory lists.

**This is more work for the same result, not a cheaper route.**
- The generic library (`allocN`, the start loop, `dirN`, `BootFacts` over a list) is needed either way. It is most
  of the cost.
- The fully generic `Main k` adds only the vocabulary of names and addresses (`decStr`, injectivity,
  `netAddrLit_loop`, already probed). It saves two extra `Main`/`Adequacy` sets, about 1-1.5 days each.

The fallback is real only if one of these breaks:
- `Main k` itself fails: the translation of the loop that builds names, or the closed theorem at a parameterized
  program;
- the `UTF-8`/`netAddrLit` vocabulary turns out much harder than probed.

Neither looks likely after the probes. If one does fail, the fallback keeps all the library work.

## 2. What is 3-specific today

Classification:
- **G** = already generic;
- **M** = mechanical to generalize;
- **D** = a real design problem.

| Item | Where | Class | Note |
|---|---|---|---|
| `Config` with `Name1..3`, `Peer1..3`, `Client1..3`, `Bridge1..3` | `examples/lib/cluster3/cluster3.go:43-59` | M | becomes `Members []Member` (§4) |
| `StartCluster`: three `StartMember`s, three `StartBridge`s, map literal | `cluster3.go:194-232` | M (Go), **D-lite** (proof) | a loop. Its loop invariant is the one new proof pattern (§6 S4) |
| `NewClient` over three bridges | `cluster3.go:238` | G | `etcdstart.NewClients` already takes a slice (`XS/lib/etcdstart/NewClients.lean:41`) |
| `PeerStep`, `ClientStep`, `Partitioner` | `cluster3.go:136-189` | G | already index slices with bounds checks |
| putget3's `Main`: three `StartMember`s, map of three | `examples/etcd/putget3/putget3.go:36-58` | M | loop over `k` |
| `alloc3`, `alloc3Http` | `X/lib/etcdstart/Alloc3.lean:180,322` | M | **probed**: `memberBoots_of`, `newServerNames_allocL`, `ΦsOf` (§5) |
| `pfx_ne`, `id_ne`, `id_nz` (three-way) | `Alloc3.lean:54-82` | G/M | `idPfxsOf_ok` already gives `Nodup` on a list. The three-way forms go away |
| `netHttp_reserve3` | `E/api/rafthttp/TransportState.lean:91` | M | **probed**: `netHttp_reserveL` over any address list |
| `alloc3On`, `alloc3OnHttp` (auth3) | `X/lib/etcdstart/Alloc3On.lean:131,248` | M | the same as `allocN`, with the mode-`on` allocators. For authN only |
| `BootFacts id₁ id₂ id₃` (putget3) | `X/etcd/putget3/Defs.lean:58` | M | `BootCore ps ctxs bl ∧ ps.Perm ids`. `BootFacts.idLow`/`idLow0` become `BootCore`'s own fields through `perm` |
| `bootPremise` per member, `premises N id₁ id₂ id₃` | `Defs.lean:141,167` | M | `bootPremise` is already per member. `premises` becomes `[∗list] i ∈ range k` |
| `urlsOk`, `initURLs3` (three-entry map) | `Defs.lean:100,107` | M | `initMap` = the insert-fold of the `k` names. `initURLsN` = lookup by name. `StartMember.spec` already takes any `Uok` and map `M` (`XS/lib/etcdstart/StartMember.lean:36-50`) |
| `etcdstart.urls3` | `X/lib/etcdstart/Defs.lean:95` | M | `urlsN` over a name list |
| `dir3`, `dir3_host`, `dir3_ok`, `dir3_dirsOk` | `X/etcd/putget3/Defs.lean:114`, `Main.lean:53-116`; `X/lib/cluster3/Defs.lean:124`, `Dir.lean:28-80` | M | `dirN ids`: an id's index, then its peer address. Needs `ids.Nodup` and `decStr_inj` |
| `utf8Keys_insert … (by decide)` ×3 | `X/etcd/putget3/Main.lean:276` | M | a lemma: ASCII names are valid UTF-8, folded over the names |
| `leaseIdsApart [id₁, id₂, id₃]` | `Alloc3.lean:191,331`; `XS/lib/cluster3/StartCluster.lean:70` | G | `leaseIdsApart` is defined over a list (`E/SrvRaftLog.lean:536`). It becomes `leaseIdsApart ids` |
| `addrsUnclaimed putget3Addrs`, `dataDirsAbsent [3 dirs]`, `ms` list, `(by decide)` Nodup/literal proofs | `X/etcd/putget3/Adequacy.lean:113,143,158-163` | M | lists generated from `k`. `Nodup` from `decStr_inj`. `netAddrLit` from the probed `netAddrLit_loop`. `dataDirsApart` stays a hypothesis-level predicate, pairwise over the list |
| putget3's `Main.spec`: three `memberStartRes` | `XS/etcd/putget3/Main.lean:52-57` | M | `[∗list] m ∈ msN k, memberStartRes m.1 m.2` (`etcd_adequate_members` already hands over such a list) |
| putget3's `Results`, `Adequacy`, `MainLinked`, `PkgTable`, `Init` | `X/etcd/putget3/` | M | new package `putgetN`. `PkgTable`/`Init` are generated (`etc/gen-init.py`) |
| cluster3's `WatchEnv` (`watchEnv cfg R₁ R₂ R₃`) | `X/lib/cluster3/WatchEnv.lean` (36 three-member refs) | M, larger | partitionN's watch theorem only. A `[∗list]` of member watch facts. Not needed for putgetN |
| restart (restart3) `Run` | `X/etcd/restart/Run.lean` (75 refs) | M?, unknown | restartN only; see §6 |

**In the server and raft proofs.** No item is 3-specific.
- `srvClusterBoot_alloc` returns the members' shares as `[∗list] id ∈ ps` (`E/NewServerAlloc.lean:151-183`).
- `nodeBoot γ.cl srvClusterN ps ctxs id`, `BootLog ps ctxs bl` (one conf change per member, `BootCore.boot`), the
  confchange policy (`ccBootOk (listToSet ps)`) and the quorum specs are all over `ps`.
- Member ids are not computed in Lean. They come from `bootstrapContract`'s `MemberID`.
- A search for `id₃` or `length = 3` outside `examples/` finds nothing.

## 3. Raft and server generality

**Raft.**
- The specs are over a `ConfState`/`Membership` of any voter set.
- The election-safety and log-matching invariants (`Inv*`) and the quorum lemmas (`MajorityConfig__VoteResult`,
  `__CommittedIndex`) never fix the size.
- `k = 1` is the singleton path, already proved (putget).

**Server.**
- `NewServer`'s spec takes the cluster as `γ.vs = ps` and `γ.boot = bootLog`.
- `bootstrapContract` is per member, at the member's id.
- `rafthttp.bootCfg dir ps` and `netDirOk dir` are over any directory.

**The bootstrap log.**
- It is `BootLog ps ctxs bl`, one `ConfChange` entry per peer.
- The allocation checks it once for the list: `srvBootLogOk_of_BootLog`, `bootEntries_ok`, `ccBootOk`.
- No per-`n` case exists, so the log is handled for any `n`.

Generality comes in only at the examples' allocation and start.

## 4. Go side

### A generic start

The start becomes generic in `examples/lib/etcdstart`, which putget3 already uses:

```go
// Member is one member of a new cluster: its name, peer address and client address.
type Member struct{ Name, Peer, Client string }

// Members returns the k members of a cluster named prefix: member i is prefix-i, with peer address
// 127.0.0.1:(peerBase+i) and client address 127.0.0.1:(clientBase+i) (strconv.FormatUint).
func Members(prefix string, k uint64, peerBase, clientBase uint64) []Member

// StartMembers starts the members ms of a new cluster with token token (StartMember for each, in
// order), the URLs map built from ms. Returns the servers, or an error at the first failure.
func StartMembers(ms []Member, token string, lg *zap.Logger) ([]*etcdserver.EtcdServer, error)
```

`putgetN.Main(k)` does the following:
1. `ms := etcdstart.Members("putgetN", k, 24000, 25000)`;
2. `StartMembers`;
3. `Serve(srvs[0], ms[0].Client)`;
4. then, as putget3 does: `NewClient`, `Put`, `Get`, check.

Later, `clusterN.StartCluster(cfg)` is `StartMembers` plus a loop of `StartBridge`, with
`Config{Token, Members []Member, Bridges []string, SnapCount, SnapCatchUp}`.

### Member ids and collisions

- etcd computes each id from the member's peer URLs and the cluster token (`membership.NewClusterFromURLsMap`, as
  `TestMemberIDs` does today).
- The premises generalize as is, because both are already over a list:
  - `BootCore`'s 16-bit `lowNodup`/`lowNz`;
  - `leaseIdsApart ids` for the lease variants.
- No new premise is needed.

`TestMemberIDs(k)` checks both for a given `k`:
- the 16 low bits are distinct and nonzero;
- the 15 low bits are distinct.

The test is deterministic and starts no cluster. **Recommendation:** run it for every odd `k ≤ 15` on every run.
- It costs milliseconds.
- It makes the theorem's id premise demonstrably satisfiable at each claimed `k`.
- It is not a configuration run in the sense of the user's correction below (decision Q4).

### The cluster test: one random odd `k` per run (the user's correction, 2026-11-15)

`TestPutGetN` runs the cluster once per run:
- `k` is drawn at random from {1, 3, 5, 7}.
- The environment variable `PUTGETN_MEMBERS=<k>` overrides the draw.
- The test logs the choice first: `t.Logf("putgetN: k=%d (rerun with PUTGETN_MEMBERS=%d)", k, k)`. A failure is
  then reproducible.

The run itself:
1. It runs `Main(k)` in `t.TempDir()`.
2. It then asks member 0 (via `clientv3`) whether the Put took effect.
3. It asks `MemberList` whether the cluster has `k` members.

Repeated runs (CI and the Go gates) cover several `k` over time. A `k = 7` run is seven in-process members, well
under the 32G cap of Go tests. The same random-draw pattern is reused for partitionN/authN/restartN.

## 5. Probes (scratch Lean, all sorry-free)

The probe files are:
- `Scratch/ProbeN.lean` (197 lines);
- `Scratch/ProbeAddr.lean` (107 lines).

Both are untracked, in the worktree. Copies are in `/shared/tmp/clusterN-scope/`. Both were checked with
`lake env lean`: no errors, no `sorry`. An injected error was caught, so the files were really checked.

**Probe A, `netHttp_reserveL`.** It generalizes `netHttp_reserve3` to any address list: it reserves every address
for the raft protocol, gives `□ ∀ lid, netHttpOk γn lid`, and gives `[∗list] a ∈ As, httpProtoOwn a …`.
It is proved by induction with `http.reserve`, then `netHttpOk_of_dir`. About 40 lines.

**Probe B, `newServerNames_allocL ps (hnd : ps.Nodup)`.** It produces each member's store, cok, rev and registry
names as functions of the member's id (`w64 → …`), with `[∗list] id ∈ ps` of their resources.
- The functions are built by `if id = p then … else …`.
- `Nodup` transports the tail.
- Representing the names as functions is what lets `Φs`/`xs` be defined after the allocation, as `alloc3Http`'s
  if-chains are.

**Probe C, the core of `allocN`.**
- `ΦsOf ps idx` and `xsOf ps idx` define the claimers' facts and the key registrations by
  `ps.find?` on the prefix. `ΦsOf_at`/`xsOf_at` show they give each member's own store, from `(idPfxsOf ps).Nodup`.
- `memberBoots_of` is `memberBoot_of` folded over any sublist `L`. It takes `srvClusterBoot_alloc`'s per-member
  `[∗list]`, the waits' `[∗list]` and probe B's names, and returns
  `[∗list] id ∈ L, ∃ ρ, ⌜kv agrees with γk⌝ ∗ memberBoot {γ with reg := reg id} ctxs ρ (env₀ …) Φs id cmp lm`.
- It is proved by list induction under the persistent invariants. It went through on the first attempt: the
  per-member lemma `memberBoot_of` was already the right step.

**Probe D, `netAddrLit_loop`.** It proves `1 ≤ p ≤ 65535 → netAddrLit ("127.0.0.1:" ++ decStr p) = true`, with
helpers:
- `decNumeral_decStr` (the decimal parser inverts `decStr` on positives, with no leading zero);
- `bytesSplit_noSep`;
- the digit lemmas.

This replaces the `(by decide)` on the address literals for generated addresses.

**What the probes leave.**
- `allocN` itself: assembling A to C around `srvClusterBoot_alloc` and taking the client's `etcdKV` at the head
  member. That is mechanical now.
- **The start loop's invariant (S4).** This is the remaining risk. The loop carries:
  - the `[∗list]` of the not-yet-started members' `memberBoot`/`memberFreshRes`/`bootPremise`;
  - the started servers' slice;
  - member 0's `memberUp` result, for `Serve`;
  - the thread token;
  - a URLs map built in an earlier loop, whose `ownMap` must equal the insert-fold of the names.

  `wp_for` loops are proved in the examples already (`X/lib/cluster3/Partitioner.lean:64`). What is new is the size
  of the per-iteration resources and `StartMember`'s 30-odd arguments. The estimate below allows for it.

## 6. Stages and estimates

### putgetN (recommended first)

| Stage | Content | Est. (agent-days) |
|---|---|---|
| S0 | Draft/Freeze of the statement (§1) and `etcdstart.{Members,StartMembers}.spec`; user review of `etcd_putgetN_safe`'s statement | 0.5-1 |
| S1 | Go: `Members`, `StartMembers`, `examples/etcd/putgetN`, `TestMemberIDs`, `TestPutGetN` (random `k`); Goose configuration, `etc/goose.py` | 0.5-1 |
| S2 | `allocN` (probes A-C assembled, plus the head member's `etcdKV`); `netHttp_reserveL` into `TransportState.lean` | 1-2 |
| S3 | vocabulary: `membersN`, address and directory lists, `Nodup` via `decStr_inj`, `netAddrLit_loop`, UTF-8 of names, `dirN` with its `_ok`/`_dirsOk`/`_host`, `urlsN`, `BootFacts` over a list | 1.5-2.5 |
| S4 | `StartMembers.wp_proof` (both loops) and `putgetN.Main.wp_proof` | 2.5-4 |
| S5 | `Adequacy`/`MainLinked`/`Results`, generated `PkgTable`/`Init`, a collection, interfaces, gates, landing | 1-1.5 |
| **Total** | | **7-12** (about 2-2.5 weeks of calendar time with reviews) |

`alloc3` and putget3 stay as they are. Re-deriving `alloc3` from `allocN`, or retiring putget3 in favour of
putgetN, is a later cleanup that changes no exported statement (decision Q5).

### Ports after putgetN

Each port is estimated after putgetN has landed.

| Port | What it needs | Est. |
|---|---|---|
| **clusterN** library | `StartCluster` = `StartMembers` + bridge loop; `cfgOk`, `StartRes`, `Dir`, `clusterUp` over lists; `WatchEnv` as a `[∗list]` of member watch facts | 1.5-2.5 weeks |
| **partitionN** | on clusterN; schedule indices `< k` (the Go already bounds-checks); the watch variant needs `WatchEnv` | 1-1.5 weeks |
| **auth3 → authN** | `allocNOn` (`allocN` with `srvClusterBootOn_alloc`/`memberBootOn_of`, the same shape as `alloc3On`); `run` over the member list | 1-1.5 weeks |
| **restart3 → restartN** | on clusterN's start. `Run.lean`'s restart of one member among `k`. The restart rows' discharge for three members (`srvRestartRows`, `notes/restart3-scope.md` §1) must be checked to be voter-count generic before estimating firmly | 1.5-3 weeks, **with the most risk** |

**Recommendation.** putgetN first. Then clusterN with partitionN, the most used library. Then authN, then
restartN, after a one-day check that the restart rows' proof is generic in the voter count.

## 7. Decisions needed

| # | Question | Options | Recommendation |
|---|---|---|---|
| Q1 | Parity | (a) `1 ≤ k ≤ 1000`; (b) also `k % 2 = 1` | **(a).** No step needs odd `k`, and (a) implies (b). The Go test still draws odd `k` |
| Q2 | Where `k` lives | (a) `Main(k uint64)`, one theorem; (b) a Go constant per program, one theorem each for 3/5/7 | **(a).** (b) is the fallback (§1). It reuses all the library work |
| Q3 | Bound on `k` | 1000 (ports 24000+i, 25000+i); or another fixed bound | **1000.** It is forced only by ports `≤ 65535` (`netAddrLit`) |
| Q4 | `TestMemberIDs` | (a) deterministic over all odd `k ≤ 15` on every run; (b) only the random `k` | **(a).** It starts no cluster, and it shows the id premise holds at each claimed `k`. The cluster test follows the user's random-`k` rule |
| Q5 | putget3 and `alloc3` | keep as is; or re-derive or retire later | **Keep** during putgetN. Decide on cleanup after it lands |
| Q6 | Library home | `etcdstart.{Members,StartMembers}` (shared by putgetN and clusterN); or a new `clusterN` package from the start | **`etcdstart`.** putget does not use bridges. clusterN builds on it |

## State and how to continue

- Branch `clusterN-scope` (this note only). Nothing else is built or landed.
- The probes are untracked in `Scratch/`, with copies in `/shared/tmp/clusterN-scope/`.
- To check them:
  `lake --packages=/shared/tmp/manifest-ddc.json env lean Scratch/ProbeN.lean`, the same for `ProbeAddr.lean`,
  under `systemd-run --scope -q -p MemoryMax=64G`.
- Next, after decisions Q1-Q6: S0 (Draft/Freeze of the statement and the two `etcdstart` specs).

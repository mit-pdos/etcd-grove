# txnlinfaultsN: the statement of `etcd_txnlinfaultsN_safe`, for review before linking (2026-11-15)

Branch `txnlinfaultsN`. Plan: `notes/txnlinfaultsN-plan.md` (the user's decisions of 2026-11-15 via
etcd-grove-81). Everything below the closed theorem is proved: `Main.wp_proof`, `startCluster.wp_proof`,
`bridgeAddr.wp_proof`, `holdToken.wp_proof`, over the specs of their callees (no `sorry`, no new axiom, no
trusted text). What is left is the linking (`Link`/`MainLinked`, `Adequacy`, `Results`, generated
`PkgTable`/`Init`, the collection, interfaces, gates), which waits for this statement.

## The program

`examples/etcd/txnlinfaultsN`: `Main(k, clients, ops, sched)` starts `k` etcd members in one process with the
generic start (`etcdstart.Members`: `txnlinfaultsN-0` .. `txnlinfaultsN-(k-1)`, peer addresses
`127.0.0.1:26000+i`, client addresses `127.0.0.1:27000+i`; `etcdstart.StartMembers`, at partition's snapshot
settings, `SnapCount = SnapCatchUp = 1`), serves every member's gRPC API on its client address, starts a copy
of etcd's test bridge to each (`127.0.0.1:28000+i`), connects `k` clients each to all `k` bridges (failover),
forks the partitioner on `sched` (`cluster3.Partitioner`: `CutPeer`/`MendPeer` between members `A` and `B`, both
directions; `Blackhole`/`Unblackhole`/`DropConnections` on member `A`'s bridge; a step naming a member index
`≥ k` does nothing), runs partition's `Check` (txnlin's workload: `clients` concurrent clients of `ops`
operations, gets, ranges, puts, deletes and transactions, each through a client picked at random, porcupine
against txnlin's 575-line model) and panics if porcupine answers `Illegal`. The program is
`txnlinfaultsN.initialize' #() ;; Main #(W64 k) #clients #ops (schedLit steps)`.

## The statement (Lean, as it will be in `Results.lean`)

```lean
theorem etcd_txnlinfaultsN_safe [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.txnlinfaultsN.Assumptions]
    [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]
    [go_etcd_io.etcd.client.v3.DialWithBalancerBody] [log.NewModel]
    (Hctx : ∀ hG, ContextReadErrs (hG := heapAt hG lctx))
    (Hcec : ∀ hG, ContextErrsClient (hG := heapAt hG lctx))
    (k : Nat) (hk1 : 1 ≤ k) (hk : k ≤ 1000)
    (ids ps : List w64) (ctxs : List (List w8)) (boot : List LogEntry)
    (Hlen : ids.length = k) (Hbf : etcd_txnlinfaultsN.BootFacts ids ps ctxs boot)
    (Haf : authRecordsFit) (Hbuq : apply.backendUnderQuota) (Hrf : grpcRepliesFit)
    (Hdbo : storage.diskOk)
    (clients ops : w64)
    (Hc0 : 0 ≤ sint.Z clients) (Hc31 : sint.Z clients < 2 ^ 31) (Hops : 0 ≤ sint.Z ops)
    (Hmul : sint.Z clients * sint.Z ops < 2 ^ 60)
    (steps : List github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Step)
    (Hsteps : steps.length < 2 ^ 63)
    (HNs : prometheus.namesUnclaimed (txnlinfaultsNProgram k clients ops steps) txnlinfaultsNNames)
    (HAs : addrsUnclaimed (txnlinfaultsNProgram k clients ops steps) (txnlinfaultsNAddrs k))
    (HDs : dataDirsAbsent (txnlinfaultsNProgram k clients ops steps) (txnlinfaultsNDirs k))
    (HEnv : verifyEnvOff (txnlinfaultsNProgram k clients ops steps))
    (n : Nat)
    (Hprem : ∀ hG, ⊢ etcd_txnlinfaultsN.premises (hG := heapAt hG lctx) k n ids ps ctxs boot)
    (σ : state) (g : GlobalState) (Hlctx : σ.goState.goLctx = lctx) (Hinit : IsInit σ)
    (Hthreads : σ.threads = 1)
    (κs : List Observation) (t2 : List Expr) (σ2 : CfgState)
    (Hsteps' : RealNsteps n ([txnlinfaultsNProgram k clients ops steps], ((σ, g) : CfgState)) κs (t2, σ2))
    (Hn : n + 2 ≤ 2 ^ 28) :
    (∀ v t2', t2 = Val v :: t2' → v = #(go!"Ok") ∨ v = #(go!"Unknown")) ∧
    (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
    (∀ v, Val v ∈ t2 → v.isPanic = false)
```

with `txnlinfaultsNAddrs k` the `3k` addresses (the peer, client and bridge addresses), `txnlinfaultsNDirs k`
the `k` data directories `txnlinfaultsN-i.etcd`, `txnlinfaultsNNames` the read package's two metric names
(putget3's and partition's), and `etcd_txnlinfaultsN.premises k n ids ps ctxs boot` (`Defs.lean`): for each
member, `bootstrap`'s contract at its name, URLs and id, at the directory naming each member's one peer URL;
`proto.Marshal`'s contract at the bootstrap log's conf changes; the raft wrapper's contracts. These are
putgetN's premises at this program's members and token (`txnlinfaultsN-6255`), and partition's
`cluster3.premises` with a list in place of three members.

## In plain words

For every member count `k` from 1 to 1000, every number of clients and operations within the bounds, and
**every schedule** of partitions (any list of steps): run the program from a fresh state with one thread, for
any number `n` of steps (`n + 2 ≤ 2^28`). Then, if the main thread has finished, it returned `Ok` or `Unknown`
(so porcupine never found a history not linearizable); no thread is stuck; no thread has panicked. This holds
if:

1. etcd's member ids for the `k` members (`ids`, in member order), the peers in `bootstrap`'s order (`ps`, a
   permutation of `ids`), the peers' contexts and the bootstrap log are what Go computes, and the ids' 16 low
   bits are distinct and not 0 (`BootFacts`, putgetN's; `TestMemberIDs` checks it for every `k ≤ 1000` at the
   token `txnlinfaultsN-6255`);
2. the size facts partition assumes: auth records fit, the backend is under quota, gRPC replies fit, the disk
   behaves;
3. `Run`'s bounds on `clients` and `ops` and the schedule's length below `2^63` (partition's);
4. at start nothing else claims the program's metric names, its `3k` addresses or its `k` data directories, and
   `ETCD_VERIFY` is off;
5. the trust-boundary contracts per member (`premises`), the context and client error classes (`Hctx`,
   `Hcec`), and the class instances, all as partition's.

## Compared with `etcd_partition_safe` and `etcd_putgetN_safe`

| | `etcd_partition_safe` | `etcd_putgetN_safe` | `etcd_txnlinfaultsN_safe` |
|---|---|---|---|
| members | 3 | `k`, `1 ≤ k ≤ 1000` | `k`, `1 ≤ k ≤ 1000` |
| ids | `id₁ id₂ id₃`, putget3's `BootFacts` | `ids`, `Hlen`, putgetN's `BootFacts` | putgetN's (`ids`, `Hlen`, `BootFacts`) |
| workload | txnlin via `partition.Check` | one Put, one Get | partition's (`partition.Check`, the same code) |
| faults | `CutPeer`/`MendPeer`, bridge cuts, any schedule | none | partition's, any schedule over indices `< k` |
| snapshots | `SnapCount = SnapCatchUp = 1` | off | `SnapCount = SnapCatchUp = 1` |
| addresses | 9 | `k + 1` | `3k` |
| `clients`/`ops`/`steps` bounds | yes | n/a | partition's, unchanged |
| result | `Ok` or `Unknown`, no stuck thread, no panic | `#()`, no stuck thread, no panic | partition's |

**New premises: none.** Every premise is partition's, with putgetN's generalization of the three members to a
list: `1 ≤ k ≤ 1000` and `ids.length = k` (putgetN's), `BootFacts` over a list (putgetN's), `premises` over the
members' list, and the address and directory lists generated from `k`. The theorem has no watch variant
(partition's `etcd_partition_watch_safe` is not part of this goal).

## Decisions for the reviewer

1. Approve the statement above (the name is the user's).
2. `etcdstart.StartMembers` gained the snapshot settings (`snapCount`, `catchUp`; it now calls `NewMember` and
   `Start` per member, as `StartMember` did): without them the members could not take partition's snapshots
   (the snapshot catch-up path partition's `TestMainRun` asserts). putgetN's Go program now passes
   `NoSnapCount`/`NoSnapCatchUp` (the values `StartMember` used): the program text of `etcd_putgetN_safe` changes,
   its behavior and its statement do not; its `Main.wp_proof` re-checked. Recommendation: accept.
3. Bounds gate: +6 (`spec-thread` 2, `spec-receipt` 4 in txnlinfaultsN: the `Main`/`startCluster` pass-throughs,
   putgetN's and partition's pattern). Recommendation: accept, as for putgetN.

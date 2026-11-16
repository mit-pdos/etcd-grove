# txnlinfaultsN: `etcd_partition_safe` for k members (2026-11-15, for etcd-grove-81)

**The user's decisions (2026-11-15).** `etcd_txnlinfaultsN_safe` (the name is fixed): partition's theorem for
`k` members, over the generic start that landed with `etcd_putgetN_safe` (`etcdstart.Members`/`StartMembers`),
replacing a "partitionN" port. It keeps txnlin's robustness workload (lintest.Run of concurrent clients doing
gets, ranges, puts, deletes and transactions, each through a random member, checked by porcupine against
txnlin's model), etcd's own fault injection (`CutPeer`/`MendPeer` between members, the bridge's
`Blackhole`/`Unblackhole`/`DropConnections` between each member and its clients) on a schedule `Main` is given,
and "for every schedule". It should hold for every `1 ≤ k ≤ 1000`, as putgetN.

## The program (`examples/etcd/txnlinfaultsN`)

`Main(k, clients, ops, sched)`: `k = 0` returns `Unknown`; `startCluster(k)`; `go cluster3.Partitioner`;
`partition.Check(clis, clients, ops, 0)`; a panic on `Illegal`. `startCluster`:
- `etcdstart.Members("txnlinfaultsN", k, 26000, 27000)`: member `i` is `txnlinfaultsN-i`, peer address
  `127.0.0.1:(26000+i)`, client address `127.0.0.1:(27000+i)`;
- `etcdstart.StartMembers(ms, Token, SnapCount, SnapCatchUp, lg)` at partition's snapshot settings (1, 1): so
  that a member a cut kept behind is caught up by a snapshot. `StartMembers` gained the two snapshot
  parameters for this (it calls `NewMember` and `Start` per member instead of `StartMember`); putgetN passes
  `NoSnapCount`/`NoSnapCatchUp`, its behavior unchanged;
- per member, in order: `go holdToken()` (its thread token is the one the member's serving takes,
  cluster3's pattern), `etcdstart.Serve(srvs[i], ms[i].Client)`, `cluster3.StartBridge(bridgeAddr(i),
  ms[i].Client)` with `bridgeAddr(i) = 127.0.0.1:(28000+i)`;
- `k` clients, each `etcdstart.NewClients(baddrs)` of all `k` bridges (failover, D27).

The workload and partitioner are imported, not copied: `partition.Check` (and its `Apply`) and
`cluster3.Partitioner`, whose specs are over lists already; their proofs are reused unchanged.

The token `txnlinfaultsN-6255` is the first `txnlinfaultsN-<i>` at which the ids' 16 low bits are distinct and
not 0 for every `k ≤ 1000` (the ids depend on the peer URLs, so putgetN's token does not carry over).
`TestMemberIDs` checks every `k ≤ 1000`. `TestMainRun` draws `k` from {1, 3, 5, 7} (`TXNLINFAULTSN_MEMBERS`
overrides it) and runs partition's schedule generalized to `k` members (each member isolated in turn for 3 s,
a client blackhole, unblackhole and drop), asserting porcupine `Ok`, agreement of every member, the member
count and, for `k > 1`, a leader change, a follower caught up by entries, a log compaction and a snapshot sent.

## The proof (`Proof/.../examples/etcd/txnlinfaultsN/`)

- `Defs`: `members k`, `bridgeAt`, `bridges k`, `startOf`, `BootFacts` (putgetN's), `premises` (putgetN's at
  this program's members and token, putgetN's directory `dirN`), `clusterUp` (the started cluster as lists:
  servers, bridges, clients, and the members as the clients reach them, `client.SrvAt` at the bridges).
- `Dir`: the pure facts (names, ports, plain endpoints, the `3k` addresses distinct literals, the data
  directories).
- `startCluster.wp_proof`: putgetN's allocation (`allocN`, every member with its client address),
  `StartMembers`, then the serve-and-bridge loop and the clients loop.
- `Main.wp_proof`: partition's `Main` over the lists.

What is left after the statement review: linking (`Link`/`MainLinked`, `Adequacy` with
`etcd_adequate_members` and `Bs = bridges k`, `Results`, generated `PkgTable`/`Init`, the collection,
interfaces, gates). See `notes/txnlinfaultsN-handoff.md`.

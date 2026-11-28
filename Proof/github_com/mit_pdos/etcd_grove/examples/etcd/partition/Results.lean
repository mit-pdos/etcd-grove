/-
The partitioned three-member instance's results (`examples/etcd/partition/linkv3p.go`; the partition
plan, `notes/partition-plan.md`), restated, with the trust base of each printed in the build log
(`#print axioms`). Lean-first (no Rocq counterpart).

* **`linkv3p_Main`** (`Link.lean`'s `etcd_partition.wp_Main`): `Main(clients, ops, sched)` -- three etcd
  members started in process and served (`startMember`), a copy of etcd's test bridge to each
  member's client address (`127.0.0.1:2385{1,2,3}` to `127.0.0.1:2383{1,2,3}`, since 2026-10-21),
  three clients (etcd's default retries, D31) each of all three bridges (failover: each attempt to one member, grpc's
  balancer's choice, D27), the partitioner forked on the schedule `sched` (the links
  between members cut and mended, in both directions, with etcd's own `CutPeer`/`MendPeer`, and
  the links between each client and its member blackholed, unblackholed or dropped, with the
  bridge's `Blackhole`/`Unblackhole`/`DropConnections`, as its steps say), linkvtxn's `Check` (gets, lists, puts, deletes, transactions and
  compare-and-sets against the model of etcd's KV; linkv's Puts and Gets until 2026-10-20) with
  each operation through one of the three clients (each attempt to the member grpc's balancer
  picks, D27), and a panic if porcupine answers `Illegal` -- does
  not panic and returns `Ok` or `Unknown`, **for every schedule** (`sched ↦*□ steps`, any
  `steps`). From `isPkgInit linkv3p`, the right to listen on
  the nine addresses, the main thread's token and `Main`'s named premises
  (`Spec/github_com/mit_pdos/etcd_grove/examples/etcd/partition/Main.lean`).

* **`linkv3p_MainWatch`** (`Link.lean`'s `etcd_partition.wp_MainWatch`; W4 of
  `notes/watch-cut-plan.md`, 2026-10-22): `MainWatch(nw, nops, sched)` -- watchkv's workload over
  the cluster: the writers' puts picked, the cluster started (`startCluster`), a prefix watch from
  revision `1` through the first client, the partitioner forked on the schedule, `nw` writers
  through clients picked at random, the watch read up to the highest successful put and checked
  against the writes -- does not panic and returns `WatchOk`, `WatchFailed` or `WatchEnded`, for
  every schedule. From the same resources as `Main`.

What the theorem says of partitions: the network model (`Transport.Start`'s axiom) lets any
message be lost, so the proofs of raft and of etcd's server never needed delivery; this program
is the one in which messages *are* lost, on the schedule's say, with clients at every member,
and the theorem is that every history it produces is still linearizable (D24, the
transport's remotes: the hooks' axioms take a member of a new cluster). The same holds of the
links between the clients and their members (`notes/client-cut-plan.md`): each client reaches
every member, through a copy of etcd's test bridge per member, which is part of the network (D26: trust-boundary
specs, its code not verified): it relays a prefix of each side's bytes, which gRPC sees as the
member's server or as a failed attempt, as any connection. A blackholed bridge is never blackholed
again (its `Blackhole` panics on a second call, `nonissues/etcd-bridge-blackhole-twice-panic.md`).
Each client is configured with every member's bridge (failover, D27): each attempt of a call goes
to one member, and the reply is that member's; the client's results take the conjunction of the
members' specs (`Proof/go_etcd_io/etcd/client/v3/Results.lean`, "The client's KV calls").

**The closed theorems retired (2026-11-21, the user's decision D2 of `notes/etcd-unified-scope.md`).**
Its closed theorems `etcd_partition_safe` and `etcd_partition_watch_safe` (with their `_adequate` and `_robust`
forms, `Adequacy.lean`, `AdequacyWatch.lean`, `PkgTable.lean`, `TopLevelDefs.lean` and the `TopLevelRobustness.lean`
pair) are gone: the one closed etcd theorem `etcd_safe` (`examples/etcd/all`,
`Proof/github_com/mit_pdos/etcd_grove/examples/etcd/all/Results.lean`) runs `MainWatch`, and txnlinfaultsN's
`Main` (in it) covers `Main`'s workload at three members (`notes/etcd-unified-scope.md` §1.3, §4); the function triples here stay.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.partition.Link

@[expose] public section

set_option pp.fullNames true
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section results
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.partition.Assumptions]
variable [NaInvG GF]

/-- **`Main` does not panic, for every schedule** (`Link.lean`'s `etcd_partition.wp_Main`). -/
theorem linkv3p_Main :
    etcd_partition.Main.spec (GF := GF) (hG := hG) :=
  etcd_partition.wp_Main

/-- **`MainWatch` does not panic, for every schedule** (`Link.lean`'s `etcd_partition.wp_MainWatch`; W4
of `notes/watch-cut-plan.md`). -/
theorem linkv3p_MainWatch :
    etcd_partition.MainWatch.spec (GF := GF) (hG := hG) :=
  etcd_partition.wp_MainWatch

end results

#print axioms linkv3p_Main
#print axioms linkv3p_MainWatch

end EtcdGrove
end Perennial

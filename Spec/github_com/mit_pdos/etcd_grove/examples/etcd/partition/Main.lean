/-
`Main(clients, ops, sched)` (`examples/etcd/partition/linkv3p.go`; the partition plan's S3b, 2026-10-20):
three etcd members started in process and served (`cluster3.StartMember`, on linkv3p's names and ports), a
bridge to each member's client address (`cluster3.StartBridge`, etcd's test bridge), three clients (etcd's
default retries) each connected to all three bridges (`cluster3.NewClient`; failover since 2026-10-21, D27), the partitioner forked on the schedule `sched` (`go
cluster3.Partitioner(srvs, brs, sched)`: the links between members cut and mended, and the links between
each client and its member blackholed, unblackholed or dropped, as its steps say, any steps;
`notes/client-cut-plan.md`), and `Check(clis, clients, ops, 0)` (linkvtxn's KV workload since 2026-10-20, linkv's
before; each operation through one of the clients, to the member grpc's balancer picks), with a panic if porcupine reports the history `Illegal`. Lean-first (no Rocq
counterpart).

**The triple:** from the package's `isPkgInit`, the right to listen on the nine addresses
(`netAddrFree`, D19d: the members' peer and client addresses, the bridges'), the schedule read-only (`sched ↦*□ steps`, for *every* list of steps), the
main thread's token and `Main`'s named premises (`etcd_partition.premises`: putget3's at linkv3p's
configuration, `Proof/.../linkv3p/Defs.lean`), `Main(clients, ops, sched)` does not panic and
returns `Ok` (the check ran: the history is linearizable) or `Unknown` (a step before the check
failed).

**The pure premises:** linkv3's (`linkv3.Main.spec`: putget3's with the member ids and the peers
`ps` in `bootstrap`'s order, `etcd_partition.BootFacts`, and `Run`'s bounds on `clients` and `ops`) plus v3rpc's method sets
(`v3rpc.ServerMethodSets`, which serving every member takes). Stated under the cache package's
assumptions, as putget3's.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.cluster3.StartRes
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.partition.Defs
public import Proof.go_etcd_io.etcd.client.v3.ErrorsNewOk

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_partition

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.partition.Assumptions]

/-- See the file header. -/
abbrev Main.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions]
    [EtcdGrove.ContextReadErrs (GF := GF) (hG := hG)]
    [ContextErrsClient (GF := GF) (hG := hG)]
    (N : Nat) (id₁ id₂ id₃ : w64) (ps : List w64) (ctxs : List (List w8)) (boot : List LogEntry)
    (clients ops : w64) (sched : GoSlice)
    (steps : List github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Step),
  BootFacts id₁ id₂ id₃ ps ctxs boot →
  threadBound GF ≤ 2 ^ 28 →
  -- (per-type stage B3) the levels of a thread token the members' gRPC runs use
  srvLevels (GF := GF) → receiptBound GF ≤ 2 ^ 48 → receiptBound GF ≤ N + 1 →
  -- (2026-11-03, the whole-`bootOk` review, A) the write budget `bootstrap`'s own write-backs leave
  N + 7 + bootWB ≤ backend.wbInit →
  ckptEffectsOk → authRecordsFit → apply.backendUnderQuota → grpcRepliesFit →
  storage.diskOk → v3rpc.ServerMethodSets →
  errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty →
  0 ≤ sint.Z clients → sint.Z clients < 2 ^ 31 → 0 ≤ sint.Z ops →
  sint.Z clients * sint.Z ops < 2 ^ 60 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.partition ∗
      -- (2026-11-05, hub step 7, D1) the cluster's start bundle: each member's (its WAL directory
      -- fresh, its peer and client addresses free, the peer's HTTP protocol unregistered) and the
      -- bridges' addresses free
      cluster3.startRes (GF := GF) clusterCfg ∗
      sched ↦*□ steps ∗ threadTok ∗ premises N id₁ id₂ id₃ ps ctxs boot }}
    (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.partition.Main)) (Val #clients))
      (Val #ops)) (Val #sched))
  {{ (r : GoString), RET #r; ⌜r = go!"Ok" ∨ r = go!"Unknown"⌝ }}

end spec

end etcd_partition
end EtcdGrove
end Perennial

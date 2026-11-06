/-
`startCluster(lg)` (`examples/etcd/partition/linkv3p.go`; W4 of `notes/watch-cut-plan.md`, 2026-10-22):
`Main`'s start (until W4 inline in it): the cluster's configuration (`config`), the three members
started and served and a bridge to each member's client address (`cluster3.StartCluster`; until
2026-11-05 this package's `startMember` and `startBridge`), three clients each of every bridge
(`cluster3.NewClient`, over `etcdstart.NewClients`; failover, D27). Lean-first (no Rocq
counterpart).

**The triple:** from the package's `isPkgInit`, the right to listen on the nine addresses, the
thread token and `Main`'s named premises (`etcd_partition.premises`), `startCluster(lg)`, at a logger
`lg` (not null), returns the members, the bridges, the clients and
`ok`: `false` (a step failed, nothing else promised), or `true` with the thread token and the
cluster up (`clusterUp`: every member at its bridge with its KV and watch registrations, every
bridge owned and not blackholed, every client `clientv3.New`'s over the three bridges at the
watch environment of the prefix `pfx`, the caller's choice, and etcd's KV at the start store).

**The pure premises:** `cluster3.StartCluster`'s (`Main`'s but its bounds on `clients` and `ops`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.cluster3.StartRes
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.partition.Defs

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
abbrev startCluster.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions]
    (N : Nat) (id₁ id₂ id₃ : w64) (ps : List w64) (ctxs : List (List w8)) (boot : List LogEntry) (lg : Loc)
    (pfx : GoString),
  BootFacts id₁ id₂ id₃ ps ctxs boot →  lg ≠ null →
  threadBound GF ≤ 2 ^ 28 → receiptBound GF ≤ 2 ^ 48 → receiptBound GF ≤ N + 1 →
  -- (2026-11-03, the whole-`bootOk` review, A) the write budget `bootstrap`'s own write-backs leave
  N + 7 + bootWB ≤ backend.wbInit →
  ckptEffectsOk → authRecordsFit → apply.backendUnderQuota → grpcRepliesFit →
  storage.diskOk → v3rpc.ServerMethodSets →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.partition ∗
      -- (2026-11-05, hub step 7, D1) the cluster's start bundle: each member's (its WAL directory
      -- fresh, its peer and client addresses free, the peer's HTTP protocol unregistered) and the
      -- bridges' addresses free
      cluster3.startRes (GF := GF) clusterCfg ∗
      threadTok ∗ premises N id₁ id₂ id₃ ps ctxs boot }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.partition.startCluster)) (Val #lg))
  {{ (srvs brs clis : GoSlice) (ok : Bool), RET (PairV (PairV (PairV #srvs #brs) #clis) #ok);
      ⌜ok = false⌝ ∨
      (⌜ok = true⌝ ∗ threadTok ∗ clusterUp id₁ id₂ id₃ (LogEntry.toEntries boot 0) pfx srvs brs clis) }}

end spec

end etcd_partition
end EtcdGrove
end Perennial

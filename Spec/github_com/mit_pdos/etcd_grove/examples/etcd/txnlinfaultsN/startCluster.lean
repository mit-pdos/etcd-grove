/-
`startCluster(k, lg)` (`examples/etcd/txnlinfaultsN/txnlinfaultsN.go`; partition's `startCluster`
over `k` members, `notes/txnlinfaultsN-plan.md`): the `k` members started
(`etcdstart.Members`, `etcdstart.StartMembers` at partition's snapshot settings), then each member's
gRPC server on its client address (`etcdstart.Serve`, with a `holdToken` goroutine whose thread token
the member's serving takes) and a bridge to it (`cluster3.StartBridge`), then `k` clients of every
bridge (`etcdstart.NewClients`). Lean-first (no Rocq counterpart).

**The triple:** from the package's `isPkgInit`, the logger a zap logger, the members' start bundles
(each its WAL directory fresh, its peer and client addresses free, the peer's HTTP protocol
unregistered), the bridges' addresses free, the thread token and the cluster's named premises
(`premises`), `startCluster(k, lg)` returns the members, the bridges, the clients and `ok`: `false`
(a step failed, nothing else promised), or `true` with the thread token and the cluster up
(`clusterUp`).

**The pure premises:** putgetN's `Main`'s (the member count, the ids, `BootFacts`, the budgets)
and v3rpc's method sets (`etcdstart.Serve`'s).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.StartRes
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.txnlinfaultsN.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_txnlinfaultsN

open Iris Iris.BI go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.txnlinfaultsN.Assumptions]

/-- See the file header. -/
abbrev startCluster.spec : Prop :=
  ∀ (k N : Nat) (ids : List w64) (ps : List w64) (ctxs : List (List w8)) (boot : List LogEntry)
    (lg : Loc),
  1 ≤ k → k ≤ 1000 → ids.length = k →
  BootFacts ids ps ctxs boot →
  threadBound GF ≤ 2 ^ 28 →
  srvLevels (GF := GF) → receiptBound GF ≤ 2 ^ 48 → receiptBound GF ≤ N + 1 →
  N + 7 + bootWB ≤ backend.wbInit →
  authRecordsFit → apply.backendUnderQuota → grpcRepliesFit → storage.diskOk →
  v3rpc.ServerMethodSets →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.txnlinfaultsN ∗
      zapLoggerOk lg ∗
      ([∗list] m ∈ startOf (members k), etcdstart.memberStartRes (GF := GF) m.1 ⟨some m.2.1, m.2.2⟩) ∗
      ([∗list] b ∈ bridges k, netAddrFree (GF := GF) b) ∗
      threadTok ∗ premises k N ids ps ctxs boot }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.txnlinfaultsN.startCluster))
      (Val #(W64 k))) (Val #lg))
  {{ (srvs brs clis : GoSlice) (ok : Bool), RET (PairV (PairV (PairV #srvs #brs) #clis) #ok);
      ⌜ok = false⌝ ∨
      (⌜ok = true⌝ ∗ threadTok ∗ clusterUp k (LogEntry.toEntries boot 0) srvs brs clis) }}

end spec

end etcd_txnlinfaultsN
end EtcdGrove
end Perennial

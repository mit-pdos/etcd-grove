/-
`Main(k, clients, ops, sched)` (`examples/etcd/txnlinfaultsN/txnlinfaultsN.go`,
`notes/txnlinfaultsN-plan.md`): partition's `Main` over `k` members -- the cluster started
(`startCluster`), the partitioner forked on the schedule (`cluster3.Partitioner`), partition's
`Check` of `clients` concurrent clients of `ops` operations each, and a panic if porcupine answers
`Illegal` -- does not panic and returns `Ok` or `Unknown`, **for every schedule** (`sched ↦*□ steps`,
any `steps`) and every member count `1 ≤ k ≤ 1000`. Lean-first (no Rocq counterpart).

**The premises:** partition's `Main.spec`'s, with putgetN's member count, ids and `BootFacts` in
place of the three ids; the start bundles of the `k` members (every client address served) and the
bridges' addresses free in place of `cluster3.startRes`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.StartRes
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.txnlinfaultsN.Defs
public import Proof.go_etcd_io.etcd.client.v3.ErrorsNewOk

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
abbrev Main.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions]
    (k N : Nat) (ids : List w64) (ps : List w64) (ctxs : List (List w8)) (boot : List LogEntry)
    (clients ops : w64) (sched : GoSlice)
    (steps : List github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Step),
  1 ≤ k → k ≤ 1000 → ids.length = k →
  BootFacts ids ps ctxs boot →
  threadBound GF ≤ 2 ^ 28 →
  srvLevels (GF := GF) → receiptBound GF ≤ 2 ^ 48 → receiptBound GF ≤ N + 1 →
  N + 7 + bootWB ≤ backend.wbInit →
  authRecordsFit → apply.backendUnderQuota → grpcRepliesFit →
  storage.diskOk → v3rpc.ServerMethodSets →
  errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty →
  0 ≤ sint.Z clients → sint.Z clients < 2 ^ 31 → 0 ≤ sint.Z ops →
  sint.Z clients * sint.Z ops < 2 ^ 60 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.txnlinfaultsN ∗
      ([∗list] m ∈ startOf (members k), etcdstart.memberStartRes (GF := GF) m.1 ⟨some m.2.1, m.2.2⟩) ∗
      ([∗list] b ∈ bridges k, netAddrFree (GF := GF) b) ∗
      sched ↦*□ steps ∗ threadTok ∗ premises k N ids ps ctxs boot }}
    (App (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.txnlinfaultsN.Main))
      (Val #(W64 k))) (Val #clients)) (Val #ops)) (Val #sched))
  {{ (r : GoString), RET #r; ⌜r = go!"Ok" ∨ r = go!"Unknown"⌝ }}

end spec

end etcd_txnlinfaultsN
end EtcdGrove
end Perennial

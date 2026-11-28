/-
`Main(k)` (`examples/etcd/leaseN/leaseN.go`; `notes/leaseN-plan.md`, 2026-11-16): `k` etcd members started
in process, each serving its raft handler on its own peer listener and its gRPC API on its client
address, and the lease example's two reads at every member. Lean-first (no Rocq counterpart).
`etcd_lease`'s `Main.spec` for `k` members, on putgetN's start.

**The triple:** for a member count `1 ≤ k ≤ 1000`, from the package's `isPkgInit`, the members' start
bundles (`startOf (members k)`: each member's WAL directory fresh and the right to listen on its peer
address with its HTTP protocol unregistered and on its client address), the main thread's token and
`Main`'s named premises (`etcd_leaseN.premises`), `Main(k)` returns: it does not panic, so at every
member a listing that answered listed no lease twice and a `TimeToLive(7)` that answered was about
lease `7`.

**The pure premises:** putgetN's, with the `k` members' ids `ids` (in the members' order) and the
bootstrap log Go computes (`etcd_putgetN.BootFacts`), and `etcd_lease`'s deployment premise
`leasePeersOk`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.StartRes
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.leaseN.Defs
public import Proof.go_etcd_io.etcd.client.v3.TimeoutCtx

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_leaseN

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.leaseN.Assumptions]

/-- See the file header. -/
abbrev Main.spec : Prop :=
  ∀ (k N : Nat) (ids : List w64) (ps : List w64) (ctxs : List (List w8))
    (boot : List LogEntry),
  1 ≤ k → k ≤ 1000 → ids.length = k →
  etcd_putgetN.BootFacts ids ps ctxs boot →
  threadBound GF ≤ 2 ^ 28 →
  srvLevels (GF := GF) → receiptBound GF ≤ 2 ^ 48 → receiptBound GF ≤ N + 1 →
  N + 7 + bootWB ≤ backend.wbInit →
  authRecordsFit → apply.backendUnderQuota → grpcRepliesFit → storage.diskOk →
  leasePeersOk →
  v3rpc.ServerMethodSets →
  errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.leaseN ∗
      ([∗list] m ∈ startOf (members k), etcdstart.memberStartRes (GF := GF) m.1 ⟨some m.2.1, m.2.2⟩) ∗
      threadTok ∗ premises k N ids ps ctxs boot }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.leaseN.Main)) (Val #(W64 k)))
  {{ RET #(); True }}

end spec

end etcd_leaseN
end EtcdGrove
end Perennial

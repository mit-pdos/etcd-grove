/-
`Main(k)` (`examples/etcd/leaseexpiryN/leaseexpiryN.go`; `notes/leaseN-plan.md`, 2026-11-16): `k` etcd members started
in process, each serving its raft handler on its own peer listener and its gRPC API on its client
address, a lease of the minimum TTL granted through every member, and at every member, once its
listing no longer lists the lease granted through it, one more listing. Lean-first (no Rocq
counterpart). `etcd_leaseexpiry`'s `Main.spec` for `k` members, on putgetN's start.

**The triple:** for a member count `1 ≤ k ≤ 1000`, from the package's `isPkgInit`, the members' start
bundles (`startOf (members k)`: each member's WAL directory fresh and the right to listen on its peer
address with its HTTP protocol unregistered and on its client address), the main thread's token and
`Main`'s named premises (`etcd_leaseexpiryN.premises`), `Main(k)` returns: it does not panic, so at every
member, once a listing did not list the lease granted through it, the next listing did not either.

**The pure premises:** putgetN's, with the `k` members' ids `ids` (in the members' order) and the
bootstrap log Go computes (`etcd_putgetN.BootFacts`), the ids' 15 low bits distinct (`leaseIdsApart`: the
members' lease ids apart), and `etcd_leaseexpiry`'s deployment premise `leasePeersOk`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.StartRes
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.leaseexpiryN.Defs
public import Proof.go_etcd_io.etcd.client.v3.TimeoutCtx

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_leaseexpiryN

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.leaseexpiryN.Assumptions]

/-- See the file header. -/
abbrev Main.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions]
    (k N : Nat) (ids : List w64) (ps : List w64) (ctxs : List (List w8))
    (boot : List LogEntry),
  1 ≤ k → k ≤ 1000 → ids.length = k →
  etcd_putgetN.BootFacts ids ps ctxs boot → leaseIdsApart ids →
  threadBound GF ≤ 2 ^ 28 →
  srvLevels (GF := GF) → receiptBound GF ≤ 2 ^ 48 → receiptBound GF ≤ N + 1 →
  N + 7 + bootWB ≤ backend.wbInit →
  authRecordsFit → apply.backendUnderQuota → grpcRepliesFit → storage.diskOk →
  leasePeersOk →
  v3rpc.ServerMethodSets →
  errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.leaseexpiryN ∗
      ([∗list] m ∈ startOf (members k), etcdstart.memberStartRes (GF := GF) m.1 ⟨some m.2.1, m.2.2⟩) ∗
      threadTok ∗ premises k N ids ps ctxs boot }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.leaseexpiryN.Main)) (Val #(W64 k)))
  {{ RET #(); True }}

end spec

end etcd_leaseexpiryN
end EtcdGrove
end Perennial

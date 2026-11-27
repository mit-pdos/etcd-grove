/- Lean-first (no Rocq counterpart).

`MainCluster(k, clients, ops, watchers, wops)` (`examples/k8s/etcd3/k8setcd3.go`; stage A of
`notes/k8s-7f6-scope.md`, 2026-11-16: `k` members, the user's decision (b)): `Main` over a
`k`-member cluster. The cluster and its client (`startCluster(k)`: the members on
`etcdstart.Members`/`StartMembers`, each behind a bridge, a kubernetes client of the `k` bridges
configured as etcd's clients are in practice: `etcdstart`'s dial and keepalive timeouts, the default
retries), the seed keys (`seed`), the Kubernetes etcd3 store over the client (`etcd3.New`, as
`Main`'s) and `Check(s, st0, h0, clients, ops, watchers, wops, 0)`, with a panic if porcupine reports the history
`Illegal`. `k = 0` returns `Unknown`.

**The triple:** from the package's `isPkgInit`, the members' start bundles (each member's WAL
directory fresh, its peer and client addresses free, the peer's HTTP protocol unregistered), the
bridges' addresses free, the main thread's token and the cluster's named premises
(`k8s_etcd3N.premises`), `MainCluster(k, clients, ops, watchers, wops)` does not panic and returns `Ok` (the check
ran: the history is linearizable) or `Unknown` (a step before the check failed). The pure premises
are `Main`'s (`Main.spec`), with `1 ≤ k ≤ 1000`, the ids in the members' order and the cluster's
boot facts (`k8s_etcd3N.BootFacts`, putgetN's) for the one member's. The bounds the adequacy theorem
fixes (`threadBound`, `receiptBound`) are instance binders (`ThreadBoundLe`, `ReceiptBoundLe`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.StartRes
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.ClusterN
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.MainDefs
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.ObjSpec
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Calls

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

/-- See the file header. -/
abbrev MainCluster.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] [k8s_io.apiserver.pkg.storage.etcd3.Assumptions]
    [k8s_io.apimachinery.pkg.runtime.Assumptions] [k8s_io.apimachinery.pkg.runtime.schema.Assumptions]
    [k8s_io.apiserver.pkg.storage.Assumptions] [k8s_io.apiserver.pkg.storage.value.Assumptions]
    (k N : Nat) (ids : List w64) (ps : List w64) (ctxs : List (List w8)) (boot : List LogEntry)
    (clients ops watchers wops : w64)
    [ThreadBoundLe GF (2 ^ 28)] [ReceiptBoundLe GF (2 ^ 48)] [ReceiptBoundLe GF (N + 1)],
  -- (per-type stage B3) the levels of a thread token the members' gRPC runs use
  srvLevels (GF := GF) →
  1 ≤ k → k ≤ 1000 → ids.length = k →
  k8s_etcd3N.BootFacts ids ps ctxs boot →
  N + 7 + bootWB ≤ backend.wbInit →
  authRecordsFit → apply.backendUnderQuota → grpcRepliesFit →
  storage.diskOk → v3rpc.ServerMethodSets →
  errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty → storageErrTyOk →
  objTyOk →
  0 ≤ sint.Z clients → 0 ≤ sint.Z watchers → sint.Z clients + sint.Z watchers < 2 ^ 31 →
  0 ≤ sint.Z ops → 0 ≤ sint.Z wops →
  sint.Z clients * sint.Z ops + sint.Z watchers * sint.Z wops < 2 ^ 60 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 ∗
      ([∗list] m ∈ k8s_etcd3N.startOf (k8s_etcd3N.members k),
        etcdstart.memberStartRes (GF := GF) m.1 ⟨some m.2.1, m.2.2⟩) ∗
      ([∗list] b ∈ k8s_etcd3N.bridges k, netAddrFree (GF := GF) b) ∗
      threadTok ∗ k8s_etcd3N.premises k N ids ps ctxs boot }}
    (App (App (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.MainCluster))
      (Val #(W64 k))) (Val #clients)) (Val #ops)) (Val #watchers)) (Val #wops))
  {{ (r : GoString), RET #r; ⌜r = go!"Ok" ∨ r = go!"Unknown"⌝ }}

end spec

end k8s_etcd3
end EtcdGrove
end Perennial

/-
`etcd3.Compact(ctx, client, expectVersion, rev)` (`k8s.io/apiserver/pkg/storage/etcd3/compact.go`):
one round of Kubernetes' etcd compactor (K2 of `notes/k8s-compactor-plan.md`, Draft 2 approved by
the user 2026-11-04; the shapes in `CompactorDefs.lean`). Lean-first (no Rocq counterpart).

The round's transaction (`casTxn ev rev`) through the client of the members `ms` (`isNewClient`,
writes sent at most once), with the caller's update at each member (`casOk`). On success (the key's
version was `ev`) at `rev ≠ 0`, the client's `Compact(rev)`. The post gives the next round's
premises on every path (`ev = 0` or `Seen`, the header revision reached or `0`), and a reported
compaction revision recorded and reached. No panic: the else arm's `Kvs[0]` reads the key the failed
compare says is present (`casPost`). The cluster in compaction mode with no retention (`cmp`,
`cret = 0`: K1's client-only mode, `v3compactor.bootCfg_off`), so the compaction needs only the
revision reached. A `ParseInt` failure returns no revision (`crev = 0`); an error returns none.
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.etcd3.CompactorDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- See the file header. -/
abbrev Compact.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
    (cl : Loc) (ms : List (client.SrvAt GF)) (V : client.WEnv GF) (γk : KVNames)
    (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF))
    (Seen : IProp GF) (recorded : w64 → IProp GF) [Persistent Seen] [∀ c, Persistent (recorded c)]
    (ev rev : w64),
  (∀ x ∈ ms, kvSame x.γr.kv γk) → γk.cmp = true → γk.cret = 0 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.etcd3 ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
      isNewClient cl (ms.map client.SrvAt.addr) V ∗
      client.clientWriteOnce cl (ms.map client.SrvAt.addr) ∗ ([∗list] x ∈ ms, client.kvRegsAt x) ∗
      ctxOk ci cd ∗ ctxErrClient ci cd ∗
      casOk ms γk Seen recorded ∗ (⌜ev = W64 0⌝ ∨ Seen) ∗ revOk γk rev }}
    (App (App (App (App (Val (@! k8s_io.apiserver.pkg.storage.etcd3.Compact))
      (Val #(GoInterface.ok ci))) (Val #cl)) (Val #ev)) (Val #rev))
  {{ (cv cr crev : w64) (err : GoInterface), RET (PairV (PairV (PairV #cv #cr) #crev) #err);
      client.clientWriteOnce cl (ms.map client.SrvAt.addr) ∗ ([∗list] x ∈ ms, client.kvRegsAt x) ∗
      (⌜cv = W64 0⌝ ∨ Seen) ∗ revOk γk cr ∗ recRevOk γk recorded crev ∗
      ⌜err ≠ GoInterface.nil → crev = W64 0⌝ }}

end spec

end k8s
end EtcdGrove
end Perennial

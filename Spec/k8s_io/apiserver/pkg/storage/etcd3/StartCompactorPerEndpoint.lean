/-
`etcd3.StartCompactorPerEndpoint(client, compactInterval)` (`compact.go`): the compactor of the
client's cluster, one per process (Q1 (c) of `notes/k8s-compactor-plan.md`). Lean-first (no Rocq
counterpart).

Under the package's registry lock (`endpointsMapMu`, the package fact `registryFact`): if one of the
client's endpoints (`Endpoints()`) has a compactor registered, that one; otherwise a new one
(`NewCompactor`, at a `RealClock`, with an `onClose` that removes the client's endpoints from the
registry), registered at every endpoint. The caller holds a claim of each of its endpoints for its
cluster `γk` and its `recorded` (`epOf ep γk recorded`, made from the claims' authority,
`epOf_alloc`): so a compactor found, whichever call registered it, with whatever client, is one of
`γk` and `recorded` (the claims agree). The new compactor's premises are `NewCompactor`'s. Returns a
compactor of `γk` and `recorded` (its client `cl'` maybe another call's) and the lower bound `0` on
its revision.
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.etcd3.CompactorDefs
public import Proof.k8s_io.apiserver.pkg.storage.etcd3.RegistryDefs

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
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [sync_sem : sync.Assumptions]

/-- See the file header. -/
abbrev StartCompactorPerEndpoint.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
    (cl : Loc) (ms : List (client.SrvAt GF)) (V : client.WEnv GF) (γk : KVNames)
    (Seen : IProp GF) (recorded : w64 → IProp GF) [Persistent Seen] [∀ c, Persistent (recorded c)]
    (iv : w64),
  (∀ x ∈ ms, kvSame x.γr.kv γk) → γk.cmp = true → γk.cret = 0 → iv ≠ W64 0 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.etcd3 ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
      isNewClient cl (ms.map client.SrvAt.addr) V ∗
      client.clientWriteOnce cl (ms.map client.SrvAt.addr) ∗ ([∗list] x ∈ ms, client.kvRegsAt x) ∗
      clientKvOk cl γk ∗ clientWatchOk cl γk ∗
      casOk ms γk Seen recorded ∗ keyReadOk γk recorded ∗
      [∗list] ep ∈ ms.map client.SrvAt.addr, epOf ep γk recorded }}
    (App (App (Val (@! k8s_io.apiserver.pkg.storage.etcd3.StartCompactorPerEndpoint)) (Val #cl))
      (Val #iv))
  {{ (c : Loc), RET #c; ∃ (cl' : Loc) (γc : CompactorNames),
      isCompactor c cl' γk recorded γc ∗ compactRevLb γc (W64 0) }}

end spec

end k8s
end EtcdGrove
end Perennial

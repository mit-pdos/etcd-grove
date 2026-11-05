/-
`(*compactor).runWatchLoop(stopCh)` (`k8s.io/apiserver/pkg/storage/etcd3/compact.go`): the
compactor's watch loop, which the feature gate `ListFromCacheSnapshot` starts (Q1 (b) of
`notes/k8s-compactor-plan.md`, the user's approval of D1-D3 2026-11-04; the shapes in
`CompactorDefs.lean`). Lean-first (no Rocq counterpart).

Under `wait.ContextForChannel(stopCh)` (`stopCh` the compactor's stop channel), each second until
the channel closes: `getCompactRev` (the key's value, the revision read), its revision recorded
(`UpdateCompactRevision`), then a watch of the key from the revision read (the client's watcher,
`clientWatchOk`, with the read update of `keyReadOk`), each response's revision recorded
(`fromWatchResponse`). Errors are logged (`klog.Errorf`). It returns once the channel is closed.
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
variable [reg : EtcdGrove.k8s.CompactorRegistry]

/-- See the file header. -/
abbrev compactor.runWatchLoop.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
    (c cl : Loc) (eps : List GoString) (V : client.WEnv GF) (γk : KVNames)
    (recorded : w64 → IProp GF) (γc : CompactorNames) (sc : GoChan) (γs : ChanNames),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.etcd3 ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
      compactorCore c cl γk recorded γc ∗ compactorChanOk c sc γs ∗
      isNewClient cl eps V ∗ clientKvOk cl γk ∗ clientWatchOk cl γk ∗ keyReadOk γk recorded }}
    (App (Val (c @!! go.GoType.PointerType k8s_io.apiserver.pkg.storage.etcd3.compactor.ty @!!
      go!"runWatchLoop")) (Val #sc))
  {{ RET #(); True }}

end spec

end k8s
end EtcdGrove
end Perennial

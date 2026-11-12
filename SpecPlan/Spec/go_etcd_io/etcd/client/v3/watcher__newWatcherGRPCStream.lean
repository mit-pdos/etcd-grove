/-
`(*watcher).newWatcherGRPCStream(inctx)`: a stream over `WithCancel(&valCtx{inctx})` (`valCtx_ctxOk`, `Context.WithCancel.spec`, `ctxPrin_child`), its channels, `run` forked (with `wgsRun` at `RunM.init` and `wgsDoneTok`). Users: `Watch`, `RequestProgress` (under `mu`).
Internal (`WatchInternal.lean`'s vocabulary). **Changes** from `specs-ref`'s file of the same
name: restated over this branch's vocabulary (the old `isWGS`, `WEnv`, `watchSrvFacts` gone).
verify-round (W3): `clientReady c` turns the handle's gated stub into the `remoteWatchAt` that
`wgsAt` keeps for `run`'s `openWatchClient`; `streamKeyFromCtx.spec` (for `ctxKey`) takes the
`ctxPrin` already here.
**Margin**: mirrors the code.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.client.v3.WatchInternal

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace ClientV3

open Iris Iris.BI EtcdModel EtcdWire
open Classical

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `w.newWatcherGRPCStream(inctx)`: a new stream of the watcher, its `run` started. -/
def watcher.newWatcherGRPCStream.spec : Prop :=
  ∀ (w c : Loc) (γ : Cluster) (who p : Principal) (inctx : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ watcherHandle w c γ who ∗
      clientReady c ∗ Context.ctxOk inctx ∗ ctxPrin who inctx p }}
    (App (Val (w @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.watcher.ty @!! go!"newWatcherGRPCStream")) (Val #inctx))
  {{ (s : Loc), RET #s; wgsAt s w γ p }}

end spec

end ClientV3
end EtcdGrove
end Perennial

/-
`(*watchGRPCStream).newWatcherStreamBufLogger(ws, now)`: a `blockLogger` (`newBlockLogger.spec`) whose callback logs `ws`'s fields (`w.lg.Info`, zap). Users: `run` (with `time.Now`).
Internal (`WatchInternal.lean`'s vocabulary). **Changes** from `specs-ref`'s file of the same
name: restated over this branch's vocabulary (the old `isWGS`, `WEnv`, `watchSrvFacts` gone).
**Margin**: mirrors the code.
-/
module

public import Spec.go_etcd_io.etcd.client.v3.WatchInternal

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

/-- `s.newWatcherStreamBufLogger(ws, now)`. -/
def watchGRPCStream.newWatcherStreamBufLogger.spec : Prop :=
  ∀ (s w ws : Loc) (γ : Cluster) (who : Principal) (wq : WatchReq) (now : GoFunc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ wgsAt s w γ who ∗ wsAt ws s γ who wq ∗ nowFuncOk now }}
    (App (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.watchGRPCStream.ty @!! go!"newWatcherStreamBufLogger")) (Val #ws)) (Val #now))
  {{ (bl : Loc), RET #bl; bufLoggerAt bl ws }}

end spec

end ClientV3
end EtcdGrove
end Perennial

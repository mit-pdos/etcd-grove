/-
`(*watchGRPCStream).recordBufWait(ws)`: records the wait (`blockLogger.recordWait.spec`) and resets it (`ws.bufLogger`, `ws.bufWaitStartTime`: in `wsOwn`). Users: `serveSubstream`.
Internal (`WatchInternal.lean`'s vocabulary). **Changes** from `specs-ref`'s file of the same
name: restated over this branch's vocabulary (the old `isWGS`, `WEnv`, `watchSrvFacts` gone).
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

/-- `s.recordBufWait(ws)`: the substream's fields as they were, but its logging clock. -/
def watchGRPCStream.recordBufWait.spec : Prop :=
  ∀ (s w ws : Loc) (γ : Cluster) (who : Principal) (q : WsM),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ wgsAt s w γ who ∗ wsOwn ws s γ who q }}
    (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.watchGRPCStream.ty @!! go!"recordBufWait")) (Val #ws))
  {{ RET #(); wsOwn ws s γ who q }}

end spec

end ClientV3
end EtcdGrove
end Perennial

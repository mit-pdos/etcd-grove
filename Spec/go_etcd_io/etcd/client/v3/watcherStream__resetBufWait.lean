/-
`(*watcherStream).resetBufWait()`: clears `bufWaitStartTime`. Users: `serveSubstream`, `recordBufWait`.
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

/-- `ws.resetBufWait()`. -/
def watcherStream.resetBufWait.spec : Prop :=
  ∀ (ws s : Loc) (γ : Cluster) (who : Principal) (q : WsM),
  {{ wsOwn (GF := GF) ws s γ who q }}
    (App (Val (ws @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.watcherStream.ty @!! go!"resetBufWait")) (Val #()))
  {{ RET #(); wsOwn ws s γ who q }}

end spec

end ClientV3
end EtcdGrove
end Perennial

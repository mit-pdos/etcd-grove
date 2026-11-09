/-
`(*watchGRPCStream).joinSubstreams()`: waits for every substream goroutine (`<-ws.donec`). Users: `run`'s teardown, `newWatchClient`.
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

/-- `s.joinSubstreams()`. -/
def watchGRPCStream.joinSubstreams.spec : Prop :=
  ∀ (s : Loc) (γ : Cluster) (who : Principal) (r : RunM),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ wgsRun s γ who r }}
    (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.watchGRPCStream.ty @!! go!"joinSubstreams")) (Val #()))
  {{ RET #(); wgsRun s γ who { r with joined := true } }}

end spec

end ClientV3
end EtcdGrove
end Perennial

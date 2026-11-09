/-
`(*watchGRPCStream).openWatchClient()`: `remote.Watch(ctx, callOpts...)` (`remoteWatchAt_watch`) until a stream, a halting error (`isHaltErr`, 1c), or the stream's context done. Users: `newWatchClient`.
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

/-- `s.openWatchClient()`: a new gRPC stream, both halves, or an error. -/
def watchGRPCStream.openWatchClient.spec : Prop :=
  ∀ (s w : Loc) (γ : Cluster) (who : Principal),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ wgsAt s w γ who }}
    (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.watchGRPCStream.ty @!! go!"openWatchClient")) (Val #()))
  {{ (wc err : GoInterface), RET (PairV #wc #err);
      (⌜err = GoInterface.nil⌝ ∗ ∃ g : WatchStreamNames,
         wireWatchSend wc γ who g [] ∗ wireWatchRecv wc γ who g WireSt.init) ∨
      (⌜err ≠ GoInterface.nil⌝ ∗ ∃ k, callErr err k) }}

end spec

end ClientV3
end EtcdGrove
end Perennial

/-
`(*watchGRPCStream).serveWatchClient(wc)`: a goroutine: each `Recv`'s response on `respc` (with its `wireStep` facts, `wireWatchRecv_recv`), its error on `errc` (buffered: one), or `donec`. Users: `newWatchClient`.
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

/-- `s.serveWatchClient(wc)`: never panics. -/
def watchGRPCStream.serveWatchClient.spec : Prop :=
  ∀ (s w : Loc) (γ : Cluster) (who : Principal) (wc : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ wgsAt s w γ who ∗ wgsRecv s γ who wc }}
    (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.watchGRPCStream.ty @!! go!"serveWatchClient")) (Val #wc))
  {{ RET #(); True }}

end spec

end ClientV3
end EtcdGrove
end Perennial

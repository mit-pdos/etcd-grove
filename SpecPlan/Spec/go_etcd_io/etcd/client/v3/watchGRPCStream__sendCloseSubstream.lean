/-
`(*watchGRPCStream).sendCloseSubstream(ws, resp)`: a goroutine: the final error response on `outc` (or the watch's context done, or 250 ms), then `outc` closed (`wsCloser`: the one right to do both). Users: `closeSubstream`.
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

/-- `s.sendCloseSubstream(ws, resp)`: never panics. -/
def watchGRPCStream.sendCloseSubstream.spec : Prop :=
  ∀ (s ws : Loc) (γ : Cluster) (who : Principal) (resp : Loc)
    (v : go_etcd_io.etcd.client.v3.WatchResponse) (mw : WatchRespM),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ wsCloser ws s γ who mw ∗ resp ↦ v ∗ watchRespAt v mw }}
    (App (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.watchGRPCStream.ty @!! go!"sendCloseSubstream")) (Val #ws)) (Val #resp))
  {{ RET #(); True }}

end spec

end ClientV3
end EtcdGrove
end Perennial

/-
`(*valCtx).Done()`: the package's `valCtxCh`, never closed (`valCtx_ctxOk`). Users: `WithCancel`'s propagation.
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

/-- `vc.Done()`: the package's never-closed channel. -/
def valCtx.Done.spec : Prop :=
  ∀ (vc : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 }}
    (App (Val (vc @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.valCtx.ty @!! go!"Done")) (Val #()))
  {{ (ch : Loc), RET #ch; globalAddr go_etcd_io.etcd.client.v3.valCtxCh ↦□ ch }}

end spec

end ClientV3
end EtcdGrove
end Perennial

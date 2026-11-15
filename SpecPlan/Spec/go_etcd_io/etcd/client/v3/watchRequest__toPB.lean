/-
`(*watchRequest).toPB()`: the create request of the watch from its current `rev` (`initReq.rev`: the substream's position). Users: `run`, `newWatchClient`'s resumes.
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

/-- `wr.toPB()`: a fresh create request for the watch `w` from `rev`. -/
def watchRequest.toPB.spec : Prop :=
  ∀ (wr : Loc) (ctx : GoInterface) (w : WatchReq) (dq : DFrac) (rev : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ initReqAt wr ctx w ∗ wr.[go_etcd_io.etcd.client.v3.watchRequest, go!"rev"] ↦{dq} rev }}
    (App (Val (wr @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.watchRequest.ty @!! go!"toPB")) (Val #()))
  {{ (p : Loc), RET #p; wr.[go_etcd_io.etcd.client.v3.watchRequest, go!"rev"] ↦{dq} rev ∗
      watchReqOwn p (DFrac.own 1) (.create w (sint.Z rev)) }}

end spec

end ClientV3
end EtcdGrove
end Perennial

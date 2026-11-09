/-
`(*valCtx).Deadline()` (`client/v3/watch.go`): `zeroTime, false`: no deadline. Users: grpc, on the stream's context.
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

/-- `vc.Deadline()`: no deadline. -/
def valCtx.Deadline.spec : Prop :=
  ∀ (vc : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 }}
    (App (Val (vc @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.valCtx.ty @!! go!"Deadline")) (Val #()))
  {{ (t : time.Time) (ok : Bool), RET (PairV #t #ok); ⌜ok = false⌝ }}

end spec

end ClientV3
end EtcdGrove
end Perennial

/-
The trust boundary of `mvccpb.Event_EventType.String` (see its spec).
-/
module

public import Spec.go_etcd_io.etcd.api.v3.mvccpb.Event_EventType__String

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- The trust boundary (see the spec's file header). -/
axiom mvccpb.Event_EventType.String.wp_proof : mvccpb.Event_EventType.String.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial

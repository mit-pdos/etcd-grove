/-
The trust boundary of `(*mvccpb.Event_EventType).String` (see its spec; T5-f over the pointer receiver,
approved by the user 2026-11-15 via etcd-grove-81, `notes/k8s-7f5a-draft.md` §11.5).
-/
module

public import Spec.go_etcd_io.etcd.api.v3.mvccpb.Event_EventType__StringPtr

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
axiom mvccpb.Event_EventType.StringPtr.wp_proof : mvccpb.Event_EventType.StringPtr.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial

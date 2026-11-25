/-
The trust boundary: `proto.MarshalBootConfChange` (`google.golang.org/protobuf/proto` is names-only;
premises to axioms, item B, 2026-11-24); see the spec file for the statement and why it is true.
-/
module

public import Spec.google_golang_org.protobuf.proto.MarshalBootConfChange

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
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- **The trust boundary**: protobuf-go's `proto.Marshal` of a boot conf change, as the spec states it. -/
axiom proto.MarshalBootConfChange.wp_proof : proto.MarshalBootConfChange.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial

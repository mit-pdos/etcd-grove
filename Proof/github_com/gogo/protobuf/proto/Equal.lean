/-
The trust boundary: gogoproto's `proto.Equal` (names-only): Go reflection, not modelled; see the spec for the
reading of `equal.go` it encodes.
-/
module

public import Spec.github_com.gogo.protobuf.proto.Equal

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- **Trust boundary**: an `axiom` rather than a `sorry`, so that it counts as an assumption
under `#print axioms`. -/
axiom gogoproto.Equal.wp_proof : gogoproto.Equal.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial

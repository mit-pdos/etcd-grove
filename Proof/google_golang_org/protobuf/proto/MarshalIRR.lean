/-
The trust boundary: `proto.Marshal` of an `*etcdserverpb.InternalRaftRequest` (protobuf-go's
encoder, names-only; the decoding `irrDecode` is opaque, so this is the encoding's one fact).
-/
module

public import Spec.google_golang_org.protobuf.proto.MarshalIRR

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.api.v3.etcdserverpb.Assumptions]

axiom proto.MarshalIRR.wp_proof : proto.MarshalIRR.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial

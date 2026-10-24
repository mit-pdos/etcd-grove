/-
The trust boundary: `proto.Unmarshal` on `*etcdserverpb.InternalRaftRequest`
(`google.golang.org/protobuf` is names-only).
-/
module

public import Spec.google_golang_org.protobuf.proto.UnmarshalIRR

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI google_golang_org.protobuf go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.api.v3.etcdserverpb.Assumptions]

axiom proto.UnmarshalIRR.wp_proof : proto.UnmarshalIRR.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial

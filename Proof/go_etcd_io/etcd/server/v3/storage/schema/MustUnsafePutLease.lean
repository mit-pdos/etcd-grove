/-
The trust boundary: `schema.MustUnsafePutLease` (names-only: it encodes the lease with
`google.golang.org/protobuf/proto`'s `Marshal`, which no proof here models).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.schema.MustUnsafePutLease

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.schema.Assumptions]

axiom schema.MustUnsafePutLease.wp_proof :
  schema.MustUnsafePutLease.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial

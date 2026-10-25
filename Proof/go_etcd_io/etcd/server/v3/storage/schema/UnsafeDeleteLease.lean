/-
The trust boundary: `schema.UnsafeDeleteLease` (names-only, as `MustUnsafePutLease`; one
`UnsafeDelete` of the lease's 8-byte key: its spec's docstring).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.schema.UnsafeDeleteLease

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

axiom schema.UnsafeDeleteLease.wp_proof :
  schema.UnsafeDeleteLease.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial

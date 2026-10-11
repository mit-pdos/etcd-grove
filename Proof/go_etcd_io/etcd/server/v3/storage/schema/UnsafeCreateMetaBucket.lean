/-
The trust boundary: `schema.UnsafeCreateMetaBucket` (names-only; it creates the `Meta` bucket).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.schema.UnsafeCreateMetaBucket

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

axiom schema.UnsafeCreateMetaBucket.wp_proof :
  schema.UnsafeCreateMetaBucket.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial

/-
The trust boundary: `(*types.ID).String` (`client/pkg/v3/types` is names-only; unit N4,
2026-10-17).
-/
module

public import Spec.go_etcd_io.etcd.client.pkg.v3.types.ID__String_ptr

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

axiom types.ID.String_ptr.wp_proof : types.ID.String_ptr.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial

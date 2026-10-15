/-
The trust boundary: `types.ID.String` (`client/pkg/v3/types` is names-only).
-/
module

public import Spec.go_etcd_io.etcd.client.pkg.v3.types.ID__String

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

axiom types.ID.String.wp_proof : types.ID.String.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial

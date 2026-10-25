/-
The trust boundary: `types.IDFromString` (`client/pkg/v3/types` is names-only).
-/
module

public import Spec.go_etcd_io.etcd.client.pkg.v3.types.IDFromString

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

axiom types.IDFromString.wp_proof : types.IDFromString.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial

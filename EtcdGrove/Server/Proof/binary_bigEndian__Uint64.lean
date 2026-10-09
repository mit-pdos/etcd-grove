/-
The trust boundary: `binary.bigEndian.Uint64`. Perennial does not translate `bigEndian` (only `LittleEndian`); its proof would be
`wp_littleEndian_Uint64`'s with the bytes reversed.
-/
import EtcdGrove.Server.Spec.binary_bigEndian__Uint64

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : encoding.binary.Assumptions]

axiom binary.bigEndian.Uint64.wp_proof : binary.bigEndian.Uint64.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial

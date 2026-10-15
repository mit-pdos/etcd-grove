/-
`binary.bigEndian.PutUint64` through the global `BigEndian`: Perennial's
`encoding.binary.wp_BigEndian_PutUint64` (the big-endian encoding is the little-endian one
reversed, as `u64Be`/`beToU64`).
-/
module

public import Spec.encoding.binary.bigEndian__PutUint64
public import Perennial.Proof.encoding.binary

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
variable [package_sem : encoding.binary.Assumptions]

theorem binary.bigEndian.PutUint64.wp_proof : binary.bigEndian.PutUint64.spec (GF := GF) (hG := hG) :=
  fun b space rem v hl => encoding.binary.wp_BigEndian_PutUint64 b space rem v hl

end proof

end EtcdGrove
end Perennial

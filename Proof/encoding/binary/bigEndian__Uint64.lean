/-
`binary.bigEndian.Uint64` through the global `BigEndian`: Perennial's
`encoding.binary.wp_BigEndian_Uint64` (the big-endian encoding is the little-endian one
reversed, as `u64Be`/`beToU64`).
-/
module

public import Spec.encoding.binary.bigEndian__Uint64
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

theorem binary.bigEndian.Uint64.wp_proof : binary.bigEndian.Uint64.spec (GF := GF) (hG := hG) :=
  fun b bs rem dq hl => encoding.binary.wp_BigEndian_Uint64 b bs dq rem hl

end proof

end EtcdGrove
end Perennial

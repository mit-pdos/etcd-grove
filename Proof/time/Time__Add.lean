/-
`(*time.Time).Add`: the trust boundary (see `Spec/time/Time__Add.lean`). In Go the pointer method
is the value method on `*l` (the promoted method of a value receiver); Perennial's `Time.wp_Add`
(an axiom) covers the value receiver only. A `ptr_Add_unfold` in Perennial's `time` would replace
this axiom.
-/
module

public import Spec.time.Time__Add

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

/-- **Trust boundary**: `(*time.Time).Add` returns some time and leaves `*l` unchanged. -/
axiom time.Time.Add.wp_proof : time.Time.Add.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial

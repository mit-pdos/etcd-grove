/-
The trust boundary: `slices.Equal` on `[]string` (`Spec/slices/EqualString.lean`; not translated by
Perennial). Go's body: `if len(s1) != len(s2) { return false }; for i := range s1 { if s1[i] !=
s2[i] { return false } }; return true`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.slices.EqualString

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

axiom slices.EqualString.wp_proof : slices.EqualString.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial

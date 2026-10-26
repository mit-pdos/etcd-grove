/-
The trust boundary: `json.Unmarshal` (`encoding/json`, names only; D43 M4, 2026-10-26, the user's
decision): see the spec's docstring.
-/
module

public import Spec.encoding.json.Unmarshal

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

axiom encoding.json.Unmarshal.wp_proof : encoding.json.Unmarshal.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial

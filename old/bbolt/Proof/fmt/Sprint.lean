module
public import Spec.fmt.Sprint

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `fmt.Sprint`. An axiom: the trust boundary (`fmt` is translated names-only). -/
axiom fmt.Sprint.wp_proof : fmt.Sprint.spec (GF := GF) (hG := hG)

end proof

end bbolt
end EtcdGrove
end Perennial

module
public import Spec.log.Logger__Output

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

/-- A logger's `Output`. An axiom: the trust boundary (`Proof/log/LogModel.lean`). -/
axiom log.Logger.Output.wp_proof : log.Logger.Output.spec (GF := GF) (hG := hG)

end proof

end bbolt
end EtcdGrove
end Perennial

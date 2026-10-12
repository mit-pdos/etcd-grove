module
public import Spec.os.Exit

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

/-- `os.Exit`. An axiom: the trust boundary (`os` is translated names-only). -/
axiom os.Exit.wp_proof : os.Exit.spec (GF := GF) (hG := hG)

end proof

end bbolt
end EtcdGrove
end Perennial

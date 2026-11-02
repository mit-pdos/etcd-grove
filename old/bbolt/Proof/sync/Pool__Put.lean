module
public import Spec.sync.Pool__Put

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

/-- An axiom: the trust boundary (`Proof/sync/PoolModel.lean`). -/
axiom sync.Pool.Put.wp_proof : sync.Pool.Put.spec (GF := GF) (hG := hG)

end proof

end bbolt
end EtcdGrove
end Perennial

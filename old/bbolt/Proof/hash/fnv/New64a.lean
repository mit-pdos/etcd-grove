module
public import Spec.hash.fnv.New64a

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
variable [package_sem : go_etcd_io.bbolt.internal.common.Assumptions]

/-- A new FNV-1a hash. An axiom: the trust boundary (`Proof/hash/fnv/Model.lean`). -/
axiom fnv.New64a.wp_proof : fnv.New64a.spec (GF := GF) (hG := hG)

end proof

end bbolt
end EtcdGrove
end Perennial

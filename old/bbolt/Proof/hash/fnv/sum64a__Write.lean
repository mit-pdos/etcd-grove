module
public import Spec.hash.fnv.sum64a__Write

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

/-- Hashing bytes. An axiom: the trust boundary (`Proof/hash/fnv/Model.lean`). -/
axiom fnv.sum64a.Write.wp_proof : fnv.sum64a.Write.spec (GF := GF) (hG := hG)

end proof

end bbolt
end EtcdGrove
end Perennial

module
public import Spec.syscall.Flock

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
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- Locking a file. An axiom: the trust boundary (`Proof/os/FileModel.lean`). -/
axiom syscall.Flock.wp_proof : syscall.Flock.spec (GF := GF) (hG := hG)

end proof

end bbolt
end EtcdGrove
end Perennial

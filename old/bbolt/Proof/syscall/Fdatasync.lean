module
public import Spec.syscall.Fdatasync

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

/-- Syncing a file's data. An axiom: the trust boundary (`Proof/os/FileModel.lean`). -/
axiom syscall.Fdatasync.wp_proof : syscall.Fdatasync.spec (GF := GF) (hG := hG)

end proof

end bbolt
end EtcdGrove
end Perennial

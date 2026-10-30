module
public import Spec.io.fs.FileInfo__Size

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

/-- A file's size, from its `FileInfo`. An axiom: the trust boundary (`Proof/os/FileModel.lean`). -/
axiom fs.FileInfo.Size.wp_proof : fs.FileInfo.Size.spec (GF := GF) (hG := hG)

end proof

end bbolt
end EtcdGrove
end Perennial

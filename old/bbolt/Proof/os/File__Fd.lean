module
public import Spec.os.File__Fd

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

/-- A file's descriptor. An axiom: the trust boundary (`Proof/os/FileModel.lean`). -/
axiom os.File.Fd.wp_proof : os.File.Fd.spec (GF := GF) (hG := hG)

end proof

end bbolt
end EtcdGrove
end Perennial

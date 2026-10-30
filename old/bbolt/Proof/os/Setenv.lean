module
public import Spec.os.Setenv

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

/-- Setting the environment. An axiom: the trust boundary (a standard-library function translated
names-only). -/
axiom os.Setenv.wp_proof : os.Setenv.spec (GF := GF) (hG := hG)

end proof

end bbolt
end EtcdGrove
end Perennial

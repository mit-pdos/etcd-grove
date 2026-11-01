module
public import Spec.os.Unsetenv

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

/-- Unsetting the environment. An axiom: the trust boundary (a standard-library function translated
names-only). -/
axiom os.Unsetenv.wp_proof : os.Unsetenv.spec (GF := GF) (hG := hG)

end proof

end bbolt
end EtcdGrove
end Perennial

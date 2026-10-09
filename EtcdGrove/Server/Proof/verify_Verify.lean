/-
The trust boundary: `verify.Verify`. `verify` is names-only: `Verify` reads `ETCD_VERIFY` through `os.Getenv`.
-/
import EtcdGrove.Server.Spec.verify_Verify

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.client.pkg.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.pkg.v3.verify.Assumptions]

axiom verify.Verify.wp_proof : verify.Verify.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial

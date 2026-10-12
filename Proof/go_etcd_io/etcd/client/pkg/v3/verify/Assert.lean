/-
The trust boundary: `verify.Assert`. `verify` is names-only (its package reads `ETCD_VERIFY`;
`Assert` itself does not, but it formats its message with `fmt.Sprintf` of `...any`).
-/
module

public import Spec.go_etcd_io.etcd.client.pkg.v3.verify.Assert

@[expose] public section

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

axiom verify.Assert.wp_proof : verify.Assert.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial

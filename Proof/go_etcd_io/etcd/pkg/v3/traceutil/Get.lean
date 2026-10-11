/-
The trust boundary: `traceutil.Get` (names-only).
-/
module

public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.Get

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : context.Assumptions]

axiom traceutil.Get.wp_proof : traceutil.Get.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial

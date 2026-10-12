/-
The trust boundary: `traceutil.EnsureTrace` (names-only).
-/
module

public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.EnsureTrace

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

axiom traceutil.EnsureTrace.wp_proof : traceutil.EnsureTrace.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial

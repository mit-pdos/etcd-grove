/-
The trust boundary: `(*traceutil.Trace).AddField` (names-only).
-/
module

public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.Trace__AddField

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

axiom traceutil.Trace.AddField.wp_proof : traceutil.Trace.AddField.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial

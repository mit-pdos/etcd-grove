/-
The trust boundary: `traceutil.Tracer.Start` (otel's tracer (a no-op one unless `traceutil.Init` installs another) records spans the model does not see).
-/
module

public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.Tracer__Start

@[expose] public section

set_option linter.unusedSectionVars false

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

axiom traceutil.Tracer.Start.wp_proof : traceutil.Tracer.Start.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial

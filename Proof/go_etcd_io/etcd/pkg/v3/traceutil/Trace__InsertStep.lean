/-
The trust boundary: `traceutil.Trace.InsertStep` (translated, unit P1b, 2026-10-14). Its body
shifts the steps with an overlapping `append(t.steps[:at+1], t.steps[at:]...)` (in place when
the capacity allows: a memmove within one slice), for which Perennial's slice library has no
triple yet (`wp_slice_append` takes the source slice separately owned; `wp_slice_copy_within`
is the overlapping `copy` such a triple would rest on). The spec is the other methods' (the trace
owned, `ownTrace`, its emptiness kept); its one caller is `raftRequest`.
-/
module

public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.Trace__InsertStep

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

axiom traceutil.Trace.InsertStep.wp_proof : traceutil.Trace.InsertStep.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial

/-
The trust boundary: `Spec/k8s_io/utils/trace/New.lean` (the utility logs a trace's steps when it ran long; it returns a fresh `*Trace`). Lean-first.
-/
module

public import Spec.k8s_io.utils.trace.New

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
variable [package_sem : k8s_io.utils.trace.Assumptions]

axiom trace.New.wp_proof :
  trace.New.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial

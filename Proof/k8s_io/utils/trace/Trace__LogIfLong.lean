/-
The trust boundary: `Spec/k8s_io/utils/trace/Trace__LogIfLong.lean` (the method only logs). Lean-first.
-/
module

public import Spec.k8s_io.utils.trace.Trace__LogIfLong

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

axiom trace.Trace.LogIfLong.wp_proof :
  trace.Trace.LogIfLong.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial

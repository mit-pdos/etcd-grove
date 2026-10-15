/-
An assumption about the clock: `time.Since` of an earlier time is positive (see the spec).
-/
module

public import Spec.time.Since

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
variable [package_sem : time.Assumptions]

axiom time.Since.wp_proof : time.Since.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial

/-
Proof of `Spec/context/TODO.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.context.TODO

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : context.Assumptions]

theorem context.TODO.wp_proof : context.TODO.spec (GF := GF) (hG := hG) := by
  wp_start
  iapply HΦ
  itrivial

end proof

end EtcdGrove
end Perennial

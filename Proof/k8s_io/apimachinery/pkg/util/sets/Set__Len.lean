/-
Proof of `Spec/k8s_io/apimachinery/pkg/util/sets/Set__Len.lean`. Lean-first.
-/
module

public import Spec.k8s_io.apimachinery.pkg.util.sets.Set__Len

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace sets

open Iris Iris.BI Iris.ProofMode k8s_io.apimachinery.pkg.util.sets

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apimachinery.pkg.util.sets.Assumptions]

theorem Set.Len.wp_proof : Set.Len.spec (GF := GF) (hG := hG) := by
  intro K _ _ _ _ T _ m dq s
  wp_start as Hm
  wp_auto
  wp_apply wp_map_len (V := Elem) m s dq $$ Hm as Hm
  iapply HΦ $$ Hm

end proof

end sets
end EtcdGrove
end Perennial

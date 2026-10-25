/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/authkv/Permitted.lean`. Lean-first (no
Rocq counterpart).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.authkv.Permitted
public import Spec.github_com.mit_pdos.etcd_grove.examples.authkv.InRange

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace authkv

open Iris Iris.BI Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.authkv.Assumptions]

theorem Permitted.wp_proof (wp_InRange : InRange.spec (GF := GF) (hG := hG)) :
    Permitted.spec (GF := GF) (hG := hG) := by
  intro who k
  wp_start as #Hinit
  wp_auto
  by_cases hw : who = go!"u"
  · subst hw
    simp only [decide_true]
    wp_auto
    wp_apply wp_InRange
    by_cases hk : inRangeK k <;> simp [permittedK, hk] <;> wp_end
  · simp only [hw, decide_false]
    wp_auto
    simp [permittedK, hw]
    wp_end

end proof

end authkv
end EtcdGrove
end Perennial

/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/authkv/keyOf.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.authkv.keyOf

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace authkv

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.authkv.Assumptions]

theorem keyOf.wp_proof : keyOf.spec (GF := GF) (hG := hG) := by
  intro x who n
  wp_start
  wp_auto
  simp only [keyOfK, List.append_assoc]
  wp_end

end proof

end authkv
end EtcdGrove
end Perennial

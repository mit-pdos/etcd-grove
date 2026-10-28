/-
Lean-first (no Rocq counterpart).

The proof of `pick`: the remainder and the quotient, of a divisor not zero.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.linkvtxn.pick

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace linkvtxn

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.linkvtxn

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.linkvtxn.Assumptions]

theorem pick.wp_proof : pick.spec (GF := GF) (hG := hG) := by
  intro n m hm
  have hm' : ¬ uint.Z m = 0 := fun h => hm (by word)
  wp_start
  wp_auto
  simp only [hm', ↓reduceIte]
  wp_auto
  simp only [hm', ↓reduceIte]
  wp_auto
  iapply HΦ
  itrivial

end proof

end linkvtxn
end EtcdGrove
end Perennial

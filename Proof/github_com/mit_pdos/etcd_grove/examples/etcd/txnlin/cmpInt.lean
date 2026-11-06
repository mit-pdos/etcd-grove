/-
Lean-first (no Rocq counterpart).

The proof of `cmpInt`: its two comparisons.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.cmpInt

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_txnlin

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.etcd.txnlin

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.Assumptions]

theorem cmpInt.wp_proof : cmpInt.spec (GF := GF) (hG := hG) := by
  intro a b
  wp_start
  wp_auto
  wp_if_destruct
  · rw [show cmpW a b = .lt by simp [cmpW, cmpZ, Hif]]; dsimp only [ordW]
    iapply HΦ; itrivial
  · wp_if_destruct
    · rw [show cmpW a b = .gt by simp [cmpW, cmpZ, *]]; dsimp only [ordW]
      iapply HΦ; itrivial
    · rw [show cmpW a b = .eq by simp [cmpW, cmpZ, *]]; dsimp only [ordW]
      iapply HΦ; itrivial

end proof

end etcd_txnlin
end EtcdGrove
end Perennial

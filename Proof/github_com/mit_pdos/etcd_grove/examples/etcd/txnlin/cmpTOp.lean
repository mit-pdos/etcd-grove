/-
Lean-first (no Rocq counterpart).

The proof of `cmpTOp`: field by field.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.cmpTOp
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.cmpInt
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.cmpStr

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

theorem cmpTOp.wp_proof (wp_cmpInt : cmpInt.spec (GF := GF) (hG := hG))
    (wp_cmpStr : cmpStr.spec (GF := GF) (hG := hG)) :
    cmpTOp.spec (GF := GF) (hG := hG) := by
  intro a b
  wp_start
  simp only [cmpTOpO, compareLex, cmpOn]
  wp_auto
  wp_apply wp_cmpInt
  wp_if_destruct <;> first
    | (rw [then_of_ne _ Hif]; iapply HΦ; itrivial)
    | rw [then_of_eq _ Hif]
  wp_apply wp_cmpStr
  wp_if_destruct <;> first
    | (rw [then_of_ne _ Hif]; iapply HΦ; itrivial)
    | rw [then_of_eq _ Hif]
  wp_apply wp_cmpStr
  iapply HΦ; itrivial

end proof

end etcd_txnlin
end EtcdGrove
end Perennial

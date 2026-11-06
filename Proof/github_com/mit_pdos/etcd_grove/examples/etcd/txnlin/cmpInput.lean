/-
Lean-first (no Rocq counterpart).

The proof of `cmpInput`: field by field.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.cmpInput
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.cmpInt
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.cmpStr
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.cmpCmp
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.cmpTOp

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

theorem cmpInput.wp_proof (wp_cmpInt : cmpInt.spec (GF := GF) (hG := hG))
    (wp_cmpStr : cmpStr.spec (GF := GF) (hG := hG)) (wp_cmpCmp : cmpCmp.spec (GF := GF) (hG := hG))
    (wp_cmpTOp : cmpTOp.spec (GF := GF) (hG := hG)) :
    cmpInput.spec (GF := GF) (hG := hG) := by
  intro a b
  wp_start
  simp only [cmpInO, compareLex, cmpOn]
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
  wp_if_destruct <;> first
    | (rw [then_of_ne _ Hif]; iapply HΦ; itrivial)
    | rw [then_of_eq _ Hif]
  wp_apply wp_cmpInt
  wp_if_destruct <;> first
    | (rw [then_of_ne _ Hif]; iapply HΦ; itrivial)
    | rw [then_of_eq _ Hif]
  wp_apply wp_cmpCmp
  wp_if_destruct <;> first
    | (rw [then_of_ne _ Hif]; iapply HΦ; itrivial)
    | rw [then_of_eq _ Hif]
  wp_apply wp_cmpInt
  wp_if_destruct <;> first
    | (rw [then_of_ne _ Hif]; iapply HΦ; itrivial)
    | rw [then_of_eq _ Hif]
  wp_apply wp_cmpTOp
  wp_if_destruct <;> first
    | (rw [then_of_ne _ Hif]; iapply HΦ; itrivial)
    | rw [then_of_eq _ Hif]
  wp_apply wp_cmpTOp
  wp_if_destruct <;> first
    | (rw [then_of_ne _ Hif]; iapply HΦ; itrivial)
    | rw [then_of_eq _ Hif]
  wp_apply wp_cmpTOp
  wp_if_destruct <;> first
    | (rw [then_of_ne _ Hif]; iapply HΦ; itrivial)
    | rw [then_of_eq _ Hif]
  wp_apply wp_cmpInt
  wp_if_destruct <;> first
    | (rw [then_of_ne _ Hif]; iapply HΦ; itrivial)
    | rw [then_of_eq _ Hif]
  wp_apply wp_cmpTOp
  iapply HΦ; itrivial

end proof

end etcd_txnlin
end EtcdGrove
end Perennial

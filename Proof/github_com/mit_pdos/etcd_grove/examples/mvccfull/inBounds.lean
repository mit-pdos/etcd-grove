/- Lean-first (no Rocq counterpart). The proof of `inBounds` (two checks around the load): Draft, to come. -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.inBounds
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.check
public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccfull.AtomicLoad

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccfull

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.mvccfull

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccfull.Assumptions]

theorem inBounds.wp_proof
    (wp_check : check.spec (GF := GF) (hG := hG)) :
    inBounds.spec (GF := GF) (hG := hG) := by
  intro lo v hi what hlo
  wp_start
  wp_auto
  wp_apply wp_check
  · ipureintro; simp only [decide_eq_true_eq]; exact hlo
  try wp_auto
  wp_apply_core wp_Int64_Load_ex hi $$ [] [-]
  · iPkgInit
  imod HΦ with Hacc
  imodintro
  inext
  icases Hacc with ⟨%dq, %x, Hx, %Hvx, Hcl⟩
  iexists dq, x
  iframe Hx
  iintro Hx
  imod Hcl $$ Hx with HΦ
  imodintro
  wp_auto
  wp_apply wp_check
  · ipureintro; simp only [decide_eq_true_eq]; exact Hvx
  try wp_auto
  iexact HΦ

end proof

end mvccfull
end EtcdGrove
end Perennial

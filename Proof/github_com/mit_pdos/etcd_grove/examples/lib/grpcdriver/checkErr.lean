/- Lean-first (no Rocq counterpart).

# `checkErr`'s proof

`reached("error-set")` returns (`drvFacts`), and `errOk(err)` is `true`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.checkErr
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.errOk

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode EtcdGrove

namespace github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : Assumptions]
variable [pkg_wr : google_golang_org.protobuf.types.known.wrapperspb.Assumptions]

theorem checkErr.wp_proof (wp_errOk : errOk.spec (GF := GF) (hG := hG)) :
    checkErr.spec (GF := GF) (hG := hG) := by
  intro err
  wp_start as ⟨#Hf, #Hse, #Hsh⟩
  iunfold drvFacts at Hf
  icases Hf with ⟨%f, #Hfg, #Hfwp⟩
  try wp_auto
  wp_apply wp_errOk err $$ []
  · iframe #
  try wp_auto
  try wp_bind (App (Val #f) (Val _))
  iapply wp_wand $$ (Hfwp $$ %go!"error-set")
  iintro %v %Hv
  subst Hv
  try wp_auto
  iapply HΦ
  itrivial

end proof

end github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver
end Perennial

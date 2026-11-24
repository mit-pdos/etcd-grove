/- Lean-first (no Rocq counterpart).

# `isFailMsg`'s proof: `strings.HasPrefix`
-/
module

public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.net.rpcdriver.isFailMsg
public import Perennial.Spec.strings.HasPrefix

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace github_com.mit_pdos.etcd_grove.examples.net.rpcdriver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : Assumptions] [field_sem : net.FieldAssumptions]
variable [π : NetProtoGS]

theorem isFailMsg.wp_proof (wp_HasPrefix : strings.HasPrefix.spec (GF := GF) (hG := hG)) :
    isFailMsg.spec (GF := GF) (hG := hG) := by
  intro m
  wp_start as #Hs
  wp_auto
  wp_apply wp_HasPrefix $$ Hs
  wp_auto
  iapply HΦ
  itrivial

end proof

end github_com.mit_pdos.etcd_grove.examples.net.rpcdriver
end Perennial

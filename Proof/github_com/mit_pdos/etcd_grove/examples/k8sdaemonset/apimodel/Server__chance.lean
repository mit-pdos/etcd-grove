/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/k8sdaemonset/apimodel/Server__chance.lean`. Lean-first.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Server__chance
public import Spec.math.rand.Int63n

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace apimodel

open Iris Iris.BI Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.k8sdaemonset

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : apimodel.Assumptions]

theorem Server.chance.wp_proof (wp_Int63n : rand.Int63n.spec (GF := GF) (hG := hG)) :
    Server.chance.spec (GF := GF) (hG := hG) := by
  intro s γ cfg flag admin
  wp_start as #Hs
  iNamed Hs
  iNamed Hcfg
  wp_auto
  cases flag <;> cases admin <;> simp only [Bool.not_false, Bool.not_true] <;> wp_auto
  all_goals first
    | (iapply HΦ; ipureintro; intro h; cases h)
    | skip
  wp_apply wp_Int63n as %x %Hx
  · ipureintro; decide
  iapply HΦ
  ipureintro
  intro _
  exact ⟨rfl, rfl⟩

end proof

end apimodel
end EtcdGrove
end Perennial

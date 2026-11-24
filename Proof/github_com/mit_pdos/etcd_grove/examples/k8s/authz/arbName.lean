/-
The proof of `arbName.spec`
(`Spec/github_com/mit_pdos/etcd_grove/examples/k8s/authz/arbName.lean`). Lean-first (no Rocq
counterpart).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.authz.arbName
public import Spec.math.rand.Int63n

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_authz

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode k8s_io.apiserver.pkg.authorization.authorizer k8s_io.apiserver.pkg.authorization.union github_com.mit_pdos.etcd_grove.examples.k8s.authz EtcdGrove.authorizer EtcdGrove.union

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.authz.Assumptions]

theorem arbName.wp_proof
    (wp_Int63n : EtcdGrove.rand.Int63n.spec (GF := GF) (hG := hG)) :
    arbName.spec (GF := GF) (hG := hG) := by
  wp_start
  wp_auto
  wp_apply (wp_slice_literal (l := [go!"x", go!"y", go!"", go!"Not_A_DNS_Name", go!"x", go!"a"]))
  isplitr
  · ipureintro; rfl
  iintro %sp ⟨Hs, -⟩
  (try wp_auto)
  wp_apply wp_Int63n as %x %Hx
  · ipureintro; decide
  (try wp_auto)
  rw [ite_eq_left ⟨Hx.1, lt_of_lt_of_eq Hx.2 (by rfl)⟩]
  have hl : (sint.Z x).toNat < 6 := by
    have h6 : sint.Z (W64 6) = 6 := rfl
    have := Hx.2; rw [h6] at this; omega
  wp_apply wp_load_slice_index _ (sint.Z x) _ _ _ Hx.1 $$ [Hs] as -
  · iframe; ipureintro; exact List.getElem?_eq_getElem (by simpa using hl)
  (try wp_auto)
  iapply HΦ
  ipureintro
  have hall : ∀ s ∈ [go!"x", go!"y", go!"", go!"Not_A_DNS_Name", go!"x", go!"a"],
      s.length ≤ authzNameMax := by
    unfold authzNameMax; simp
  exact hall _ (List.getElem_mem ..)

end proof

end k8s_authz
end EtcdGrove
end Perennial

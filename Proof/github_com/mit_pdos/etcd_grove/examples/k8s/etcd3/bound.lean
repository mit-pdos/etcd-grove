module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.bound
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.parseRV
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.pastRead
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.isWrite

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Input Output Obj item mstore mcfg hnode state labelSel fieldSel)

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

theorem bound.wp_proof
    (wp_parseRV : parseRV.spec (GF := GF) (hG := hG))
    (wp_pastRead : pastRead.spec (GF := GF) (hG := hG))
    (wp_isWrite : isWrite.spec (GF := GF) (hG := hG)) :
    bound.spec (GF := GF) (hG := hG) := by
  intro x y
  wp_start as -
  wp_auto
  wp_if_destruct
  · rw [show boundL x y = W64 0 by simp_all [boundL]]
    iapply HΦ; itrivial
  have hk5 : x.Kind' ≠ W64 5 := by first | exact Hif | simpa using Hif
  wp_apply wp_parseRV as %req %err Hp
  ihave %hreq : ⌜(parseRVD x.MinRV').getD 0 = req⌝ $$ [Hp]
  · rcases hd : parseRVD x.MinRV' with _ | m <;> isimp only [hd] at Hp
    · icases Hp with ⟨-, -, %h0⟩; ipureintro; simp [h0]
    · icases Hp with %h; ipureintro; simp [h.2]
  wp_if_destruct
  · (try wp_auto)
    rw [show boundL x y = y.ErrRV' by simp_all [boundL]]
    iapply HΦ; itrivial
  have h1 : y.Err' ≠ W64 1 := by first | exact Hif | simpa using Hif
  wp_if_destruct
  · have h6 : y.Err' = W64 6 := by first | exact Hif | simpa using Hif
    wp_if_destruct
    · (try wp_auto)
      rw [show boundL x y = req - W64 1 by
        have : req ≠ W64 0 := by intro h; subst h; simp_all
        simp only [boundL, hreq, if_neg hk5, if_neg h1, if_pos h6, if_neg this]]
      iapply HΦ; itrivial
    · (try wp_auto)
      rw [show boundL x y = W64 0 by
        have : req = W64 0 := by word
        simp only [boundL, hreq, if_neg hk5, if_neg h1, if_pos h6, if_pos this]; rfl]
      iapply HΦ; itrivial
  have h6 : y.Err' ≠ W64 6 := by first | exact Hif | simpa using Hif
  wp_if_destruct
  · have h0 : y.Err' = W64 0 := by first | exact Hif | simpa using Hif
    wp_apply wp_isWrite
    cases hw : isWriteL x
    · (try wp_auto)
      wp_if_destruct
      · wp_apply wp_pastRead
        cases hp : pastReadL x req
        · (try wp_auto)
          rw [show boundL x y = y.ListRV' by simp_all [boundL]]
          iapply HΦ; itrivial
        · (try wp_auto)
          rw [show boundL x y = W64 0 by simp_all [boundL]]
          iapply HΦ; itrivial
      · (try wp_auto)
        rw [show boundL x y = W64 0 by simp_all [boundL]]
        iapply HΦ; itrivial
    · (try wp_auto)
      rw [show boundL x y = y.RV' by simp_all [boundL]]
      iapply HΦ; itrivial
  · (try wp_auto)
    rw [show boundL x y = W64 0 by simp_all [boundL]]
    iapply HΦ; itrivial

end proof

end k8s_etcd3
end EtcdGrove
end Perennial

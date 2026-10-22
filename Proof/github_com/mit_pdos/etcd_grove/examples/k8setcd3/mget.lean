module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8setcd3.mget
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8setcd3.lookup
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8setcd3.notFound
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8setcd3.objOut

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8setcd3

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.k8setcd3 (Input Output Obj item mstore mcfg state)

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8setcd3.Assumptions]

theorem mget.wp_proof (wp_lookup : lookup.spec (GF := GF) (hG := hG))
    (wp_notFound : notFound.spec (GF := GF) (hG := hG))
    (wp_objOut : objOut.spec (GF := GF) (hG := hG)) :
    mget.spec (GF := GF) (hG := hG) := by
  intro x s g
  wp_start as #Hs
  unfold storeOwn
  icases Hs with ⟨#Hk, %Hr⟩
  wp_auto
  wp_apply wp_lookup $$ [$Hk] as %it %ok ⟨-, %Hlk⟩
  obtain ⟨hit, hok⟩ : it = (lookupL g.items x.Key').1 ∧ ok = (lookupL g.items x.Key').2 := by
    rw [← Hlk]; exact ⟨rfl, rfl⟩
  cases ok
  · have hn : (lookupL g.items x.Key').2 = false := hok.symm
    cases hi : x.IgnoreNotFound'
    · (try wp_auto)
      simp only [hi]
      (try wp_auto)
      wp_apply wp_notFound
      have : mgetL x g = notFoundL g.rv x.Key' := by simp [mgetL, hn, hi]
      rw [this, ← Hr]
      iapply HΦ
      (try ipureintro; trivial)
    · (try wp_auto)
      simp only [hi]
      (try wp_auto)
      have : mgetL x g = zeroOutL := by simp [mgetL, hn, hi]
      rw [this]
      simp only [zeroOutL]
      iapply HΦ
      (try ipureintro; trivial)
  · have hn : (lookupL g.items x.Key').2 = true := hok.symm
    (try wp_auto)
    wp_apply wp_objOut
    have : mgetL x g = objOutL it.obj' := by simp [mgetL, hn, hit]
    rw [this]
    iapply HΦ
    (try ipureintro; trivial)

end proof

end k8setcd3
end EtcdGrove
end Perennial

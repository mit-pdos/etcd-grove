module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8setcd3.mcreate
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8setcd3.lookup
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8setcd3.setItem
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8setcd3.storeKey
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

theorem mcreate.wp_proof (wp_lookup : lookup.spec (GF := GF) (hG := hG))
    (wp_setItem : setItem.spec (GF := GF) (hG := hG))
    (wp_storeKey : storeKey.spec (GF := GF) (hG := hG))
    (wp_objOut : objOut.spec (GF := GF) (hG := hG)) :
    mcreate.spec (GF := GF) (hG := hG) := by
  intro x s g
  wp_start as ⟨#Hs, %Hb⟩
  unfold storeOwn
  icases Hs with ⟨#Hk, %Hr⟩
  wp_auto
  wp_apply wp_lookup $$ [$Hk] as %it %ok ⟨-, %Hlk⟩
  obtain ⟨hit, hok⟩ : it = (lookupL g.items x.Key').1 ∧ ok = (lookupL g.items x.Key').2 := by
    rw [← Hlk]; exact ⟨rfl, rfl⟩
  cases ok
  · have hn : (lookupL g.items x.Key').2 = false := hok.symm
    (try wp_auto)
    wp_apply wp_setItem s.items' g.items DFrac.discard ⟨x.Key', ⟨x.Key', x.Val', s.rv' + W64 1⟩, true⟩
      $$ [$Hk] as %out ⟨-, Hout, -⟩
    · ipureintro; exact Hb
    ipersist Hout
    (try wp_auto)
    wp_apply wp_objOut
    iapply HΦ
    have : mcreateL x g = (⟨setItemL g.items ⟨x.Key', ⟨x.Key', x.Val', g.rv + W64 1⟩, true⟩,
        g.rv + W64 1⟩, objOutL ⟨x.Key', x.Val', g.rv + W64 1⟩) := by simp [mcreateL, hn]
    rw [this, ← Hr]
    iframe Hout
    ipureintro; exact ⟨rfl, rfl⟩
  · have hn : (lookupL g.items x.Key').2 = true := hok.symm
    (try wp_auto)
    wp_apply wp_storeKey
    iapply HΦ
    have : mcreateL x g = (g, existsL x.Key') := by simp [mcreateL, hn]
    rw [this]
    iframe Hk
    ipureintro; exact ⟨Hr, rfl⟩

end proof

end k8setcd3
end EtcdGrove
end Perennial

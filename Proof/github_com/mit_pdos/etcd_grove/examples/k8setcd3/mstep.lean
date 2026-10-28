module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8setcd3.mstep
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8setcd3.mcreate
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8setcd3.mdelete
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8setcd3.mupdate
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8setcd3.mget

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8setcd3

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.k8setcd3 (Input Output Obj item mstore mcfg state)

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8setcd3.Assumptions]

theorem mstep.wp_proof (wp_mcreate : mcreate.spec (GF := GF) (hG := hG))
    (wp_mdelete : mdelete.spec (GF := GF) (hG := hG))
    (wp_mupdate : mupdate.spec (GF := GF) (hG := hG))
    (wp_mget : mget.spec (GF := GF) (hG := hG)) :
    mstep.spec (GF := GF) (hG := hG) := by
  intro x s g
  wp_start as ⟨#Hs, %Hb⟩
  wp_auto
  wp_if_destruct
  · wp_apply wp_mcreate x s g $$ [$Hs] as %s' %o ⟨#Hs', %Ho⟩
    · ipureintro; exact Hb
    iapply HΦ
    have : mstepL x g = mcreateL x g := by simp [mstepL, Hif]
    rw [this]
    iframe Hs'
    ipureintro; exact Ho
  · have h0 := Hif
    wp_if_destruct
    · wp_apply wp_mdelete x s g $$ [$Hs] as %s' %o ⟨#Hs', %Ho⟩
      iapply HΦ
      have : mstepL x g = mdeleteL x g := by simp [mstepL, h0, Hif]
      rw [this]
      iframe Hs'
      ipureintro; exact Ho
    · have h1 := Hif
      wp_if_destruct
      · wp_apply wp_mupdate x s g $$ [$Hs] as %s' %o ⟨#Hs', %Ho⟩
        · ipureintro; exact Hb
        iapply HΦ
        have : mstepL x g = mupdateL x g := by simp [mstepL, h0, h1, Hif]
        rw [this]
        iframe Hs'
        ipureintro; exact Ho
      · wp_apply wp_mget x s g $$ [$Hs]
        iapply HΦ
        have : mstepL x g = (g, mgetL x g) := by rw [mstepL, if_neg h0, if_neg h1, if_neg Hif]
        rw [this]
        iframe Hs
        ipureintro; trivial

end proof

end k8setcd3
end EtcdGrove
end Perennial

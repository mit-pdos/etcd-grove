module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.seed
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.seedOne

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Input Output Obj item mstore mcfg state)

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

theorem seed.wp_proof (wp_seedOne : seedOne.spec (GF := GF) (hG := hG)) :
    seed.spec (GF := GF) (hG := hG) := by
  intro _ _ cl ms V γs hAs hms
  wp_start as ⟨#Hnc, #Hwo, #Hregs, #Hsi, Hs⟩
  wp_auto
  ihave #Hs0 : storeOwn (mstore.mk slice.nil (W64 1)) (⟨[], W64 1⟩ : GSt) $$ []
  · iunfold storeOwn
    simp only
    isplitl
    · iapply ownSlice_nil
    ipureintro; trivial
  wp_apply (wp_seedOne cl ms V γs _ ⟨[], W64 1⟩ go!"a" σb hAs hms (by decide) (by simp))
    $$ [Hs] as %s1 %ok1 Hr1
  · iframe #
    iframe Hs
  icases Hr1 with (%Hok | ⟨%Hok, Hs, #Hst1, %Hb⟩)
  · subst Hok
    wp_auto
    iapply HΦ
    ileft; ipureintro; rfl
  subst Hok
  rw [seed_step1]
  wp_auto
  have hl1 : (setItemL [] itA).length + 1 < 2 ^ 63 := by
    rw [show setItemL [] itA = [itA] from rfl]; simp
  wp_apply (wp_seedOne cl ms V γs _ ⟨setItemL [] itA, W64 2⟩ go!"b" σs1 hAs hms (by decide) hl1)
    $$ [Hs]
    as %s2 %ok2 Hr2
  · iframe #
    iframe Hs
    iExactEq Hst1; rfl
  icases Hr2 with (%Hok | ⟨%Hok, Hs, #Hst2, %Hb⟩)
  · subst Hok
    iapply HΦ
    ileft; ipureintro; rfl
  subst Hok
  rw [seed_step2]
  iapply HΦ
  iright
  iframe Hs
  isplitr
  · ipureintro; rfl
  iExactEq Hst2; rfl

end proof

end k8s_etcd3
end EtcdGrove
end Perennial

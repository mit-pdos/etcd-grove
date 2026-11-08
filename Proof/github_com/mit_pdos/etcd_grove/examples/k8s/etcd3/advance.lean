module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.advance
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.appendHist

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

theorem advance.wp_proof
    (wp_appendHist : appendHist.spec (GF := GF) (hG := hG)) :
    advance.spec (GF := GF) (hG := hG) := by
  intro c g st s pend ps
  wp_start as ⟨#Hc, #Hs, #Hp⟩
  unfold cfgOwn
  icases Hc with ⟨#Hst, #Hh, #Hp0⟩
  ihave %Hrv := (show storeOwn (GF := GF) st s ⊢ ⌜st.rv' = s.rv⌝ by
    unfold storeOwn; iintro ⟨-, %H⟩; ipureintro; exact H) $$ Hs
  ihave %Hrv0 := (show storeOwn (GF := GF) c.st' g.st.st ⊢ ⌜c.st'.rv' = g.st.st.rv⌝ by
    unfold storeOwn; iintro ⟨-, %H⟩; ipureintro; exact H) $$ Hst
  wp_auto
  wp_if_destruct
  · have he : s.rv = g.st.st.rv := by rw [← Hrv, ← Hrv0]; exact Hif
    rw [show advanceL g.st s = ⟨s, g.st.hist⟩ by simp [advanceL, he]]
    iapply HΦ
    simp only
    isplit
    · iexact Hs
    isplit
    · iassumption
    · iexact Hp
  · wp_apply wp_appendHist $$ [$Hh $Hs] as %h' #Hh'
    (try wp_auto)
    have hne : s.rv ≠ g.st.st.rv := by rw [← Hrv, ← Hrv0]; exact Hif
    rw [show advanceL g.st s = ⟨s, g.st.hist ++ [s]⟩ by simp [advanceL, hne]]
    iapply HΦ
    simp only
    isplit
    · iexact Hs
    isplit
    · iassumption
    · iexact Hp

end proof

end k8s_etcd3
end EtcdGrove
end Perennial

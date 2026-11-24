module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.toPorcupineModel
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Model__Clone
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Model__Step
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Model__Equal

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode k8s_correctness
open github_com.anishathalye.porcupine

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

theorem toPorcupineModel.wp_proof
    (wp_Clone : k8s_correctness.Model.Clone.spec (GF := GF) (hG := hG))
    (wp_Step : k8s_correctness.Model.Step.spec (GF := GF) (hG := hG))
    (wp_Equal : k8s_correctness.Model.Equal.spec (GF := GF) (hG := hG)) :
    toPorcupineModel.spec (GF := GF) (hG := hG) := by
  intro mp init L hfit hsz0
  wp_start as #Hm
  wp_auto
  ipersist s
  wp_func_lits
  wp_auto
  iapply HΦ
  unfold isModel isEqHash
  simp only
  isplitr
  · ipureintro; trivial
  isplitr
  · -- Init
    unfold initSpec
    iintro !> %Φ' _ HΦ'
    wp_auto
    wp_apply wp_fupd
    wp_apply wp_Clone mp init $$ [] as %mp' Hm'
    · iframe #
    imod modelOwn_freeze _ _ $$ Hm' with #Hm'
    imodintro
    wp_auto
    iapply HΦ'
    simp only [realMS]
    rw [show (realM L init).init = init from rfl]
    iexists mp'
    isplitr
    · ipureintro; exact ⟨rfl, hfit, by omega⟩
    · iexact Hm'
  isplitr
  · iright
    isplitr
    · ipureintro; exact ⟨trivial, nofun⟩
    -- Step
    unfold stepSpec
    (try unfold stepPost)
    iintro %k %v %s %i %o
    iintro !> %Φ' ⟨%Hk, #Hrep, #Hio⟩ HΦ'
    ihave #Hrep0 := Hrep
    iunfold realMS at Hrep Hio
    icases Hrep with ⟨%sp, ⟨%hv, %hsf, %hsk⟩, #Hsm⟩
    icases Hio with ⟨%rq, %ro, %x, %r, ⟨%hi, %ho, %hdec, %hin⟩, #Hrq, #Hro⟩
    subst hv hi ho
    obtain ⟨⟨hf, hrv, hlim, hfl, hlo, hoo⟩, hcr, hk, hl⟩ := hin
    wp_auto
    wp_apply wp_Step sp s x rq ro r hsf hf hrv hlim (rexecL_notOther x s hrv hk hl) hfl hlo hoo
      (by omega)
      $$ [] as %b %np %cp ⟨%Hb, #Hnp, -⟩
    · iframe #
    (try wp_auto)
    iapply HΦ'
    have hstep : (realM L init).step s (boxReq rq, boxResp ro) =
        if (rstepL x s r).1 then some (rstepL x s r).2.1 else none := by
      show (match decR L (boxReq rq, boxResp ro) with
        | some v => (realS init).step s v | none => none) = _
      rw [hdec]; rfl
    iframe Hrep0
    rw [show (realMS (GF := GF) L init).M = realM L init from rfl, hstep]
    by_cases hc : (rstepL x s r).1 = true
    · simp only [hc, ↓reduceIte, Option.isSome_some]
      isplitr
      · ipureintro; rw [Hb, hc]
      · iunfold realMS
        iexists np
        iframe Hnp
        ipureintro
        exact ⟨rfl, itemsFitL_step x s r hsf hcr, by have := rstepL_size x s r; omega⟩
    · simp only [hc, Bool.false_eq_true, ↓reduceIte, Option.isSome_none]
      isplitr
      · ipureintro; rw [Hb]; simpa using hc
      · iempintro
  · -- Equal, no Hash
    isplitr
    · ipureintro; nofun
    isplitr
    · unfold equalSpec
      simp only [realMS]
      iintro %ka %kb %v %w %s %t
      iintro !> %Φ' ⟨#Hv, #Hw⟩ HΦ'
      ihave #Hv0 := Hv
      ihave #Hw0 := Hw
      icases Hv with ⟨%pa, ⟨%hva, -⟩, #Ha⟩
      icases Hw with ⟨%pb, ⟨%hvb, -⟩, #Hb⟩
      subst hva hvb
      wp_auto
      wp_apply wp_Equal pa pb s t $$ [] as %b %Hb
      · iframe #
      (try wp_auto)
      iapply HΦ'
      iframe Hv0 Hw0
      ipureintro; exact Hb.1
    · ileft
      ipureintro; trivial

end proof

end k8s_etcd3
end EtcdGrove
end Perennial

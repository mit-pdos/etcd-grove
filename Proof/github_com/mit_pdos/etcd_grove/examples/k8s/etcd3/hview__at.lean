module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.hview__at
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.histAt

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Input Output Obj item mstore mcfg hnode state hview)

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

theorem hview.at.wp_proof
    (wp_histAt : histAt.spec (GF := GF) (hG := hG)) :
    hview.at.spec (GF := GF) (hG := hG) := by
  intro v hs r
  unfold hviewOwn
  wp_start as ⟨⟨#Hh, %ss, #Hs, #Hc⟩, %Hl⟩
  wp_auto
  ihave %Hlen := ownSlice_len _ _ _ $$ Hs
  wp_if_destruct
  · have hge := Hif; clear Hif
    wp_if_destruct
    · have hk : uint.Z (r - v.lo') < uint.Z v.sts'.len := by simpa using Hif
      have hkl : sint.nat (r - v.lo') < ss.length := by rw [Hlen.1]; word
      list_elem ss (sint.nat (r - v.lo')) as s0
      have hb : 0 ≤ sint.Z (r - v.lo') ∧ sint.Z (r - v.lo') < sint.Z v.sts'.len := by word
      icases ownSlice_elem_acc (sint.Z (r - v.lo')) s0 v.sts' _ ss hb.1
        (by simpa [sint.nat] using Hs0_lookup) $$ Hs with ⟨#He, -⟩
      iterate 3 ((try simp only [hb, _root_.and_self, ↓reduceIte]); (try wp_auto))
      ispecialize Hc $$ %(sint.nat (r - v.lo')) %s0 %Hs0_lookup
      have hr : uint.nat v.lo' + sint.nat (r - v.lo') = uint.nat r := by word
      rw [hr, ← histAtL_eq_histN]
      iapply HΦ
      iexact Hc
    · (try wp_auto)
      wp_apply wp_histAt $$ [$Hh] as %sp #Hsp
      · ipureintro; exact Hl
      (try wp_auto)
      iapply HΦ
      iexact Hsp
  · (try wp_auto)
    wp_apply wp_histAt $$ [$Hh] as %sp #Hsp
    · ipureintro; exact Hl
    (try wp_auto)
    iapply HΦ
    iexact Hsp

end proof

end k8s_etcd3
end EtcdGrove
end Perennial

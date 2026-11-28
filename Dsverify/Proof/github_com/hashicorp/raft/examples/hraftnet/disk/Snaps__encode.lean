/-
(hraft_robust R3) The proof of `disk.(*Snaps).encode`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.disk.putUint64
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.disk.putBytes
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.disk.encodeConfiguration
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.disk.Snaps__encode

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.examples.hraftnet.disk.Assumptions]

open github_com.hashicorp.raft github_com.hashicorp.raft.examples.hraftnet.disk

theorem github_com.hashicorp.raft.examples.hraftnet.disk.Snaps.encode.wp_proof
    (wp_putUint64 : github_com.hashicorp.raft.examples.hraftnet.disk.putUint64.spec (GF := GF) (hG := hG))
    (wp_putBytes : github_com.hashicorp.raft.examples.hraftnet.disk.putBytes.spec (GF := GF) (hG := hG))
    (wp_encodeConfiguration :
      github_com.hashicorp.raft.examples.hraftnet.disk.encodeConfiguration.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.examples.hraftnet.disk.Snaps.encode.spec (GF := GF) (hG := hG) := by
  intro s S has mv dt
  unfold snapsMemAt encSnap
  rcases hS : S.latest with _ | ⟨m, bs⟩
  · wp_start as ⟨Hhas, Hmeta, Hdata, Hnid, %Hh⟩
    subst Hh
    wp_auto
    wp_apply (wp_putUint64 slice.nil []) $$ [] as %b0 ⟨Hb, Hcap⟩
    · isplitl
      · iapply ownSlice_nil
      · iapply ownSliceCap_nil
    wp_apply wp_putUint64 $$ [$Hb $Hcap] as %b1 ⟨Hb, Hcap⟩
    iapply HΦ
    dsimp only
    iframe
    ipureintro; first | rfl | trivial
  · wp_start as ⟨Hhas, Hmeta, Hdata, Hnid, %Hh, #Hm, #Hd⟩
    subst Hh
    iunfold metaRep at Hm
    icases Hm with ⟨%Hmf, #Hc⟩
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := Hmf
    wp_auto
    wp_apply (wp_putUint64 slice.nil []) $$ [] as %b0 ⟨Hb, Hcap⟩
    · isplitl
      · iapply ownSlice_nil
      · iapply ownSliceCap_nil
    wp_apply wp_putUint64 $$ [$Hb $Hcap] as %b1 ⟨Hb, Hcap⟩
    wp_apply wp_putUint64 $$ [$Hb $Hcap] as %b2 ⟨Hb, Hcap⟩
    wp_apply (wp_string_to_bytes mv.ID') as %sid ⟨Hsid, -⟩
    wp_apply wp_putBytes $$ [$Hb $Hcap $Hsid] as %b3 ⟨Hb, Hcap, -⟩
    wp_apply wp_putUint64 $$ [$Hb $Hcap] as %b4 ⟨Hb, Hcap⟩
    wp_apply wp_putUint64 $$ [$Hb $Hcap] as %b5 ⟨Hb, Hcap⟩
    wp_apply wp_encodeConfiguration $$ [$Hb $Hcap $Hc] as %b6 ⟨Hb, Hcap⟩
    wp_apply wp_putUint64 $$ [$Hb $Hcap] as %b7 ⟨Hb, Hcap⟩
    wp_apply wp_putBytes $$ [$Hb $Hcap $Hd] as %b8 ⟨Hb, Hcap, -⟩
    iapply HΦ
    dsimp only
    rw [h1, h2, h3, h4, h6]
    simp only [List.nil_append, List.append_assoc]
    iframe
    isplitr
    · ipureintro; first | rfl | trivial
    isplitl
    · iunfold metaRep
      isplitr
      · ipureintro; exact ⟨h1, h2, h3, h4, h5, h6, h7⟩
      iexact Hc
    iexact Hd

end proof

end Perennial

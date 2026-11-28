/-
`hraftnet.serverConns`'s proof: `NewConn` of each of `ServerAddrs()`, appended.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.serverConns
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.ServerAddrs
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.rpctransport.NewConn

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace github_com.hashicorp.raft.examples.hraftnet

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : Assumptions]
variable [π : Net.NetProtoGS]
variable [rpcsem : rpctransport.Assumptions] [net.rpc.Assumptions] [net.Assumptions]

set_option goose.wp.extras true

theorem serverConns.wp_proof
    (wp_ServerAddrs : ServerAddrs.spec (GF := GF))
    (wp_NewConn : rpctransport.NewConn.spec (GF := GF) (hG := hG)) :
    serverConns.spec (GF := GF) (hG := hG) := by
  intro W
  wp_start as ⟨#Has, %Hrb⟩
  wp_auto
  wp_apply wp_ServerAddrs as %asl ⟨%L, Hasl, %HL⟩
  subst HL
  ihave %Hasll := ownSlice_len _ _ _ $$ Hasl
  have hl6 : serverAddrs.length = 6 := rfl
  ihave HI : (∃ k : Nat, "Hctr" ∷ i_ptr ↦ W64 k ∗
      "Hcs" ∷ (∃ (cs : GoSlice) (ps : List Loc), cs_ptr ↦ cs ∗ cs ↦* ps ∗
        ownSliceCap Loc cs (DFrac.own 1) ∗ ⌜ps.length = k⌝ ∗
        [∗list] k ↦ p ∈ ps, rpctransport.isConn p W (serverAddrs.getD k go!"")) ∗
      "a" ∷ (∃ av : GoString, a_ptr ↦ av) ∗ "%Hk" ∷ ⌜k ≤ 6⌝ : IProp GF) $$ [i cs a]
  · iexists 0
    iframe
    isplitl [cs]
    · iexists slice.nil, []
      iframe cs
      isplitr
      · iapply ownSlice_nil
      isplitr
      · iapply ownSliceCap_nil
      isplitr
      · ipureintro; rfl
      iapply BigSepL.bigSepL_nil.2; itrivial
    isplitl [a]
    · iexists _; iexact a
    ipureintro; omega
  wp_for HI
  split
  · rename_i Hc
    icases Hcs with ⟨%cs, %ps, Hcp, Hps, Hcap, %Hpl, #Hpcs⟩
    icases a with ⟨%av, a⟩
    have hk : k < 6 := by simp only [decide_eq_true_eq] at Hc; rw [hl6] at Hasll; word
    list_elem serverAddrs k as ad
    (try wp_auto)
    rw [ite_eq_left_iff.mpr (by intro h; exfalso; apply h; constructor <;> word)]
    wp_apply (wp_load_slice_index asl (sint.Z (W64 k)) serverAddrs (DFrac.own 1) ad (by word))
      $$ [$Hasl] as Hasl
    · ipureintro
      have : (sint.Z (W64 (k : Int))).toNat = k := by word
      rw [this]; exact Had_lookup
    (try wp_auto)
    ihave #Hra := BigSepL.bigSepL_lookup Had_lookup $$ Has
    wp_apply (wp_NewConn W ad) $$ [$Hra] as %p #Hp
    · ipureintro; exact Hrb
    wp_apply wp_slice_literal (V := Loc) [p]
    isplitr
    · ipureintro; rfl
    iintro %lp ⟨Hl, -⟩
    wp_apply wp_slice_append (V := Loc) $$ [$Hps $Hcap $Hl] as %cs2 ⟨Hcs2, Hcap2, -⟩
    (try wp_auto)
    wp_for_post
    iframe
    iexists (k + 1)
    have hctr : W64 (k : Int) + W64 1 = W64 ((k + 1 : Nat) : Int) := by word
    rw [hctr]
    iframe
    isplitl [Hcp Hcs2 Hcap2]
    · iexists cs2, ps ++ [p]
      iframe
      isplitr
      · ipureintro; simp [Hpl]
      iapply BigSepL.bigSepL_snoc.2
      iframe Hpcs
      rw [Hpl]
      have ha : ad = serverAddrs.getD k go!"" := by simp [List.getD_eq_getElem?_getD, Had_lookup]
      rw [← ha]
      iexact Hp
    isplitl [a]
    · iexists _; iexact a
    ipureintro; omega
  · rename_i Hc
    icases Hcs with ⟨%cs, %ps, Hcp, Hps, Hcap, %Hpl, #Hpcs⟩
    have hk : k = 6 := by simp only [decide_eq_true_eq] at Hc; rw [hl6] at Hasll; word
    (try wp_auto)
    iapply HΦ
    iexists ps
    iframe Hps Hpcs
    ipureintro; omega

end proof

end github_com.hashicorp.raft.examples.hraftnet

end Perennial

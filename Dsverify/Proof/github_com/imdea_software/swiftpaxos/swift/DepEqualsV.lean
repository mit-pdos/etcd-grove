/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/DepEqualsV.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`Dep(d1).Equals(d2)` on a value receiver (newDesc's `acceptFastAndSlowAck`, FINDING SWB-16;
round 23, sv-swb): some Boolean, the lists kept. The proof is `Dep.Equals.wp_proofAny`'s
(FastAckCallees.lean) without the receiver's load.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.FastAckCalleesDefs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.DepEqualsVDefs

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section specs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps]
variable [swift.Assumptions]

end specs

section proofs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps]
variable [swift.Assumptions]

theorem swift.Dep.Equals.wp_proofAnyV : swift.Dep.Equals.specAnyV (hG := hG) := by
  intro d1 d2 dq1 dq2 l1 l2
  haveI := swift.hlog.cmdId_intoValInj (sem := sem)
  wp_start as ⟨Hd1, Hd2⟩
  wp_auto
  ihave %Hl1 := ownSlice_len $$ Hd1
  ihave %Hl2 := ownSlice_len $$ Hd2
  wp_if_destruct
  · have hlen : l1.length = l2.length := by rw [Hl1.1, Hl2.1, Hif]
    have hdl := Hif
    wp_apply (wp_map_make1 (K := swift.CommandId) (V := Unit)) as %m1 Hm1
    wp_apply (wp_map_make1 (K := swift.CommandId) (V := Unit)) as %m2 Hm2
    ihave HI : (∃ (i : w64) (s1 s2 : GMap swift.CommandId Unit), "i" ∷ i_ptr ↦ i ∗
        "Hm1" ∷ m1 ↦$ s1 ∗ "Hm2" ∷ m2 ↦$ s2 ∗
        "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z d1.len⌝ :
        IProp netDistGF) $$ [i Hm1 Hm2]
    · iexists W64 0, ∅, ∅; iframe; ipureintro; refine ⟨by word, by word⟩
    wp_for HI
    wp_if_destruct
    · have hil1 : sint.nat i < l1.length := by have := Hi.1; word
      have hil2 : sint.nat i < l2.length := by have := Hi.1; word
      obtain ⟨x, hx⟩ : ∃ x, l1[sint.nat i]? = some x := ⟨_, List.getElem?_eq_getElem hil1⟩
      obtain ⟨y, hy⟩ : ∃ y, l2[sint.nat i]? = some y := ⟨_, List.getElem?_eq_getElem hil2⟩
      have hb1 : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z d1.len := ⟨Hi.1, Hif⟩
      have hb2 : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z d2.len := ⟨Hi.1, by rw [← hdl]; exact Hif⟩
      have hix : l1[(sint.Z i).toNat]? = some x := by rw [show (sint.Z i).toNat = sint.nat i by word, hx]
      have hiy : l2[(sint.Z i).toNat]? = some y := by rw [show (sint.Z i).toNat = sint.nat i by word, hy]
      rw [ite_eq_left hb1]
      wp_apply (wp_load_slice_index (V := swift.CommandId) d1 (sint.Z i) _ _ x Hi.1) $$ [Hd1] as Hd1
      · iframe; ipureintro; exact hix
      wp_bind (App (Val (GoInstruction (Convert go.untypedBool go.bool))) _)
      iapply (wp_wand (Φ := fun v => iprop(⌜v = #(decide (x = y))⌝ ∗ d2 ↦*{dq2} l2))) $$ [Hd2]
      · rw [ite_eq_left hb2]
        wp_apply (wp_load_slice_index (V := swift.CommandId) d2 (sint.Z i) _ _ y Hi.1) $$ [Hd2] as Hd2
        · iframe; ipureintro; exact hiy
        wp_if_destruct
        · iframe; ipureintro; congr 2; cases x; cases y; simp_all
        · iframe; ipureintro; congr 2; cases x; cases y; simp_all
      iintro %v ⟨%hv, Hd2⟩
      subst hv
      wp_if_destruct
      · -- the same id at `i`
        wp_for_post
        iframe
        iexists i + W64 1, s1, s2
        iframe
        ipureintro
        refine ⟨by word, by word⟩
      · rw [ite_eq_left hb1]
        wp_apply (wp_load_slice_index (V := swift.CommandId) d1 (sint.Z i) _ _ x Hi.1) $$ [Hd1] as Hd1
        · iframe; ipureintro; exact hix
        wp_apply (wp_map_lookup2 _ _ m2 s2 x) $$ Hm2 as Hm2
        have hxy : x ≠ y := Hif
        let s1' := if (s2 !! x).isSome then s1 else <[x := ()]> s1
        let s2' := if (s2 !! x).isSome then GMap.delete x s2 else s2
        wp_bind (If _ _ _)
        iapply (wp_wand (Φ := fun v => iprop(m1 ↦$ s1' ∗ m2 ↦$ s2' ∗ d1 ↦*{dq1} l1 ∗
            seen1_ptr ↦ m1 ∗ seen2_ptr ↦ m2 ∗ dep1_ptr ↦ d1 ∗ i_ptr ↦ i ∗ ⌜v = executeVal⌝)))
          $$ [Hm1 Hm2 Hd1 seen1 seen2 dep1 i]
        · wp_if_destruct
          · rw [ite_eq_left hb1]
            wp_apply (wp_load_slice_index (V := swift.CommandId) d1 (sint.Z i) _ _ x Hi.1) $$ [Hd1] as Hd1
            · iframe; ipureintro; exact hix
            wp_apply (wp_mapDelete m2 s2 x) $$ Hm2 as Hm2
            simp only [s1', s2', Hif, ↓reduceIte]
            iframe
          · rw [ite_eq_left hb1]
            wp_apply (wp_load_slice_index (V := swift.CommandId) d1 (sint.Z i) _ _ x Hi.1) $$ [Hd1] as Hd1
            · iframe; ipureintro; exact hix
            wp_apply (wp_mapInsert _ m1 s1 x (zero_val Unit)) $$ Hm1 as Hm1
            have hc : (s2 !! x).isSome = false := by simpa using Hif
            simp only [s1', s2', hc, Bool.false_eq_true, ↓reduceIte]
            iframe
        iintro %v ⟨Hm1, Hm2, Hd1, seen1, seen2, dep1, i, %hv⟩
        subst hv
        wp_auto
        rw [ite_eq_left hb2]
        wp_apply (wp_load_slice_index (V := swift.CommandId) d2 (sint.Z i) _ _ y Hi.1) $$ [Hd2] as Hd2
        · iframe; ipureintro; exact hiy
        wp_apply (wp_map_lookup2 _ _ m1 s1' y) $$ Hm1 as Hm1
        wp_if_destruct
        · rw [ite_eq_left hb2]
          wp_apply (wp_load_slice_index (V := swift.CommandId) d2 (sint.Z i) _ _ y Hi.1) $$ [Hd2] as Hd2
          · iframe; ipureintro; exact hiy
          wp_apply (wp_mapDelete m1 s1' y) $$ Hm1 as Hm1
          wp_for_post
          iframe
          iexists i + W64 1, _, _
          iframe
          ipureintro
          refine ⟨by word, by word⟩
        · rw [ite_eq_left hb2]
          wp_apply (wp_load_slice_index (V := swift.CommandId) d2 (sint.Z i) _ _ y Hi.1) $$ [Hd2] as Hd2
          · iframe; ipureintro; exact hiy
          wp_apply (wp_mapInsert _ m2 s2' y (zero_val Unit)) $$ Hm2 as Hm2
          wp_for_post
          iframe
          iexists i + W64 1, _, _
          iframe
          ipureintro
          refine ⟨by word, by word⟩
    · wp_apply (wp_map_len_lt (K := swift.CommandId) (V := Unit) m1 s1) $$ [$Hm1] as ⟨Hm1, %hs1⟩
      wp_apply (wp_map_len_lt (K := swift.CommandId) (V := Unit) m2 s2) $$ [$Hm2] as ⟨Hm2, %hs2⟩
      wp_if_destruct
      · wp_apply (wp_map_len_lt (K := swift.CommandId) (V := Unit) m1 s1) $$ [$Hm1] as ⟨Hm1, -⟩
        iapply HΦ; iframe
      · iapply HΦ; iframe
  · iapply HΦ; iframe

end proofs

end Perennial.github_com.imdea_software.swiftpaxos

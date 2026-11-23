/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swiftnet/codec/DecMap.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
The codec's decoders of `MSync`'s maps (`rpcDec_map_swift_CommandId_*`) meet their parsers:
a fresh map holding the decoded entries, inserted in order (`insertAll`).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.codec.DecCmd
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.codec.Map

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos.examples.swiftnet

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section wps

variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics] [package_sem : examples.swiftnet.Assumptions]

theorem wp_rpcDec_map_swift_CommandId_int (b : GoSlice) (dq : DFrac) (bs : List w8) :
    {{ (b ↦*{dq} bs : IProp GF) }}
      (App (Val (@! rpcDec_map_swift_CommandId_int)) (Val #b))
    {{ (v : GoMap) (r : GoSlice) (ok : Bool), RET (PairV (PairV #v #r) #ok);
        decPost (pMap pInt) (ownMapOf ownPure) b dq bs v r ok }} := by
  wp_start as Hb
  wp_auto
  wp_apply wp_rpcGetU64 $$ Hb as %n %r %ok Hpost
  unfold decPost
  icases Hpost with (⟨%H, Hb⟩ | ⟨%a, %rest, %H, %Hown, Hrest⟩)
  · obtain ⟨H, rfl⟩ := H
    wp_auto
    iapply HΦ; ileft; iframe Hb; ipureintro; exact ⟨by simp [pMap, pList, H], rfl⟩
  · obtain ⟨H, rfl⟩ := H
    subst Hown
    icases restOf_open $$ Hrest with ⟨Hr, Hback⟩
    ihave %Hrl := ownSlice_len _ _ _ $$ Hr
    wp_auto
    wp_if_destruct
    · ihave Hb := Hback $$ Hr
      iapply HΦ; ileft; iframe Hb; ipureintro
      refine ⟨?_, rfl⟩
      simp only [pMap, pList, H, show ¬ (uint.nat n ≤ rest.length) by word, ↓reduceIte]
    · have hn : uint.nat n ≤ rest.length := by word
      wp_apply (wp_rawMap_make1 (V := w64) go.int) as %mp Hm
      ihave Hrc := restOf_close $$ [Hr Hback]
      · iframe Hr Hback
      ihave HI : (∃ (i : w64) (es : List (swift.CommandId × w64)) (gs : List (swift.CommandId × w64))
          (rc : GoSlice) (restc : List w8),
          "i" ∷ i_ptr ↦ i ∗ "Hm" ∷ rawMap mp (DFrac.own 1) gs ∗
          "Hvals" ∷ valsOwn ownPure gs (insertAll es) ∗
          "r" ∷ r_ptr ↦ rc ∗ "Hrc" ∷ restOf b dq bs rc restc ∗
          "%Hi" ∷ ⌜uint.nat i ≤ uint.nat n ∧ (gs.map Prod.fst).Nodup ∧
            pRep (pEntry pInt) (uint.nat i) rest = some (es, restc)⌝ :
          IProp GF) $$ [i Hm r Hrc]
      · iexists W64 0, [], [], r, rest
        iframe
        isplitr
        · simp only [insertAll, List.foldl_nil, valsOwn]; itrivial
        ipureintro; exact ⟨by word, List.nodup_nil, rfl⟩
      wp_for HI
      wp_if_destruct
      · icases restOf_open $$ Hrc with ⟨Hrc, Hrcback⟩
        wp_apply wp_rpcDec_swift_CommandId $$ Hrc as %x %r2 %ok2 Hpost
        unfold decPost
        icases Hpost with (⟨%H2, Hrc⟩ | ⟨%x', %rest2, %H2, %Hown, Hrest2⟩)
        · obtain ⟨H2, rfl⟩ := H2
          wp_auto
          wp_for_post
          ihave Hb := Hrcback $$ Hrc
          iapply HΦ; ileft; iframe Hb; ipureintro
          refine ⟨?_, rfl⟩
          simp only [pMap, pList, H, ite_eq_left hn]
          rw [pRep_none_le _ (uint.nat i + 1) _ _ _ (by word)]
          rw [pRep_succ, Hi.2.2]; simp [pEntry, H2]
        obtain ⟨H2, rfl⟩ := H2
        subst Hown
        icases restOf_open $$ Hrest2 with ⟨Hr2, Hback2⟩
        wp_auto
        wp_apply wp_rpcDec_int $$ Hr2 as %y %r3 %ok3 Hpost
        unfold decPost
        icases Hpost with (⟨%H3, Hr2⟩ | ⟨%y', %rest3, %H3, %Hown, Hrest3⟩)
        · obtain ⟨H3, rfl⟩ := H3
          wp_auto
          wp_for_post
          ihave Hrc := Hback2 $$ Hr2
          ihave Hb := Hrcback $$ Hrc
          iapply HΦ; ileft; iframe Hb; ipureintro
          refine ⟨?_, rfl⟩
          simp only [pMap, pList, H, ite_eq_left hn]
          rw [pRep_none_le _ (uint.nat i + 1) _ _ _ (by word)]
          rw [pRep_succ, Hi.2.2]; simp [pEntry, H2, H3]
        obtain ⟨H3, rfl⟩ := H3
        subst Hown
        ihave Hrest3 := restOf_comp $$ Hback2 Hrest3
        ihave Hrc := restOf_comp $$ Hrcback Hrest3
        wp_auto
        wp_apply wp_rawMapInsert $$ Hm as Hm
        wp_for_post
        iframe
        iexists i + W64 1, es ++ [(x, y)], map.insertL x y gs, r3, rest3
        iframe
        isplitl [Hvals]
        · rw [insertAll_snoc]
          iapply valsOwn_insert $$ [Hvals]
          iframe
          ipureintro; rfl
        ipureintro
        refine ⟨by word, map.nodup_insertL _ _ _ Hi.2.1, ?_⟩
        rw [show uint.nat (i + W64 1) = uint.nat i + 1 by word, pRep_succ, Hi.2.2]
        simp [pEntry, H2, H3]
      · have hin : i = n := by word
        subst hin
        iapply HΦ; iright; iexists insertAll es, restc
        iframe Hrc
        isplitr
        · ipureintro; refine ⟨?_, rfl⟩
          simp only [pMap, pList, H, ite_eq_left hn, Hi.2.2]
        unfold ownMapOf
        iexists gs
        iframe
        ipureintro; exact Hi.2.1

theorem wp_rpcDec_map_swift_CommandId_state_Command (b : GoSlice) (dq : DFrac) (bs : List w8) :
    {{ (b ↦*{dq} bs : IProp GF) }}
      (App (Val (@! rpcDec_map_swift_CommandId_state_Command)) (Val #b))
    {{ (v : GoMap) (r : GoSlice) (ok : Bool), RET (PairV (PairV #v #r) #ok);
        decPost (pMap (pCmd)) (ownMapOf ownCmd) b dq bs v r ok }} := by
  wp_start as Hb
  wp_auto
  wp_apply wp_rpcGetU64 $$ Hb as %n %r %ok Hpost
  unfold decPost
  icases Hpost with (⟨%H, Hb⟩ | ⟨%a, %rest, %H, %Hown, Hrest⟩)
  · obtain ⟨H, rfl⟩ := H
    wp_auto
    iapply HΦ; ileft; iframe Hb; ipureintro; exact ⟨by simp [pMap, pList, H], rfl⟩
  · obtain ⟨H, rfl⟩ := H
    subst Hown
    icases restOf_open $$ Hrest with ⟨Hr, Hback⟩
    ihave %Hrl := ownSlice_len _ _ _ $$ Hr
    wp_auto
    wp_if_destruct
    · ihave Hb := Hback $$ Hr
      iapply HΦ; ileft; iframe Hb; ipureintro
      refine ⟨?_, rfl⟩
      simp only [pMap, pList, H, show ¬ (uint.nat n ≤ rest.length) by word, ↓reduceIte]
    · have hn : uint.nat n ≤ rest.length := by word
      wp_apply (wp_rawMap_make1 (V := state.Command) state.Command.ty) as %mp Hm
      ihave Hrc := restOf_close $$ [Hr Hback]
      · iframe Hr Hback
      ihave HI : (∃ (i : w64) (es : List (swift.CommandId × sp.Cmd)) (gs : List (swift.CommandId × state.Command))
          (rc : GoSlice) (restc : List w8),
          "i" ∷ i_ptr ↦ i ∗ "Hm" ∷ rawMap mp (DFrac.own 1) gs ∗
          "Hvals" ∷ valsOwn ownCmd gs (insertAll es) ∗
          "r" ∷ r_ptr ↦ rc ∗ "Hrc" ∷ restOf b dq bs rc restc ∗
          "%Hi" ∷ ⌜uint.nat i ≤ uint.nat n ∧ (gs.map Prod.fst).Nodup ∧
            pRep (pEntry (pCmd)) (uint.nat i) rest = some (es, restc)⌝ :
          IProp GF) $$ [i Hm r Hrc]
      · iexists W64 0, [], [], r, rest
        iframe
        isplitr
        · simp only [insertAll, List.foldl_nil, valsOwn]; itrivial
        ipureintro; exact ⟨by word, List.nodup_nil, rfl⟩
      wp_for HI
      wp_if_destruct
      · icases restOf_open $$ Hrc with ⟨Hrc, Hrcback⟩
        wp_apply wp_rpcDec_swift_CommandId $$ Hrc as %x %r2 %ok2 Hpost
        unfold decPost
        icases Hpost with (⟨%H2, Hrc⟩ | ⟨%x', %rest2, %H2, %Hown, Hrest2⟩)
        · obtain ⟨H2, rfl⟩ := H2
          wp_auto
          wp_for_post
          ihave Hb := Hrcback $$ Hrc
          iapply HΦ; ileft; iframe Hb; ipureintro
          refine ⟨?_, rfl⟩
          simp only [pMap, pList, H, ite_eq_left hn]
          rw [pRep_none_le _ (uint.nat i + 1) _ _ _ (by word)]
          rw [pRep_succ, Hi.2.2]; simp [pEntry, H2]
        obtain ⟨H2, rfl⟩ := H2
        subst Hown
        icases restOf_open $$ Hrest2 with ⟨Hr2, Hback2⟩
        wp_auto
        wp_apply wp_rpcDec_state_Command $$ Hr2 as %y %r3 %ok3 Hpost
        unfold decPost
        icases Hpost with (⟨%H3, Hr2⟩ | ⟨%y', %rest3, %H3, Hown, Hrest3⟩)
        · obtain ⟨H3, rfl⟩ := H3
          wp_auto
          wp_for_post
          ihave Hrc := Hback2 $$ Hr2
          ihave Hb := Hrcback $$ Hrc
          iapply HΦ; ileft; iframe Hb; ipureintro
          refine ⟨?_, rfl⟩
          simp only [pMap, pList, H, ite_eq_left hn]
          rw [pRep_none_le _ (uint.nat i + 1) _ _ _ (by word)]
          rw [pRep_succ, Hi.2.2]; simp [pEntry, H2, H3]
        obtain ⟨H3, rfl⟩ := H3
        ihave Hrest3 := restOf_comp $$ Hback2 Hrest3
        ihave Hrc := restOf_comp $$ Hrcback Hrest3
        wp_auto
        wp_apply wp_rawMapInsert $$ Hm as Hm
        ihave Hvals := valsOwn_insert ownCmd x y y' gs (insertAll es) $$ [Hvals Hown]
        · iframe
        wp_for_post
        iframe
        iexists i + W64 1, es ++ [(x, y')], map.insertL x y gs, r3, rest3
        rw [insertAll_snoc]
        iframe
        ipureintro
        refine ⟨by word, map.nodup_insertL _ _ _ Hi.2.1, ?_⟩
        rw [show uint.nat (i + W64 1) = uint.nat i + 1 by word, pRep_succ, Hi.2.2]
        simp [pEntry, H2, H3]
      · have hin : i = n := by word
        subst hin
        iapply HΦ; iright; iexists insertAll es, restc
        iframe Hrc
        isplitr
        · ipureintro; refine ⟨?_, rfl⟩
          simp only [pMap, pList, H, ite_eq_left hn, Hi.2.2]
        unfold ownMapOf
        iexists gs
        iframe
        ipureintro; exact Hi.2.1

theorem wp_rpcDec_map_swift_CommandId_swift_Dep (b : GoSlice) (dq : DFrac) (bs : List w8) :
    {{ (b ↦*{dq} bs : IProp GF) }}
      (App (Val (@! rpcDec_map_swift_CommandId_swift_Dep)) (Val #b))
    {{ (v : GoMap) (r : GoSlice) (ok : Bool), RET (PairV (PairV #v #r) #ok);
        decPost (pMap (pList pCmdId)) (ownMapOf ownSliceOf) b dq bs v r ok }} := by
  wp_start as Hb
  wp_auto
  wp_apply wp_rpcGetU64 $$ Hb as %n %r %ok Hpost
  unfold decPost
  icases Hpost with (⟨%H, Hb⟩ | ⟨%a, %rest, %H, %Hown, Hrest⟩)
  · obtain ⟨H, rfl⟩ := H
    wp_auto
    iapply HΦ; ileft; iframe Hb; ipureintro; exact ⟨by simp [pMap, pList, H], rfl⟩
  · obtain ⟨H, rfl⟩ := H
    subst Hown
    icases restOf_open $$ Hrest with ⟨Hr, Hback⟩
    ihave %Hrl := ownSlice_len _ _ _ $$ Hr
    wp_auto
    wp_if_destruct
    · ihave Hb := Hback $$ Hr
      iapply HΦ; ileft; iframe Hb; ipureintro
      refine ⟨?_, rfl⟩
      simp only [pMap, pList, H, show ¬ (uint.nat n ≤ rest.length) by word, ↓reduceIte]
    · have hn : uint.nat n ≤ rest.length := by word
      wp_apply (wp_rawMap_make1 (V := GoSlice) swift.Dep.ty) as %mp Hm
      ihave Hrc := restOf_close $$ [Hr Hback]
      · iframe Hr Hback
      ihave HI : (∃ (i : w64) (es : List (swift.CommandId × List swift.CommandId)) (gs : List (swift.CommandId × GoSlice))
          (rc : GoSlice) (restc : List w8),
          "i" ∷ i_ptr ↦ i ∗ "Hm" ∷ rawMap mp (DFrac.own 1) gs ∗
          "Hvals" ∷ valsOwn ownSliceOf gs (insertAll es) ∗
          "r" ∷ r_ptr ↦ rc ∗ "Hrc" ∷ restOf b dq bs rc restc ∗
          "%Hi" ∷ ⌜uint.nat i ≤ uint.nat n ∧ (gs.map Prod.fst).Nodup ∧
            pRep (pEntry (pList pCmdId)) (uint.nat i) rest = some (es, restc)⌝ :
          IProp GF) $$ [i Hm r Hrc]
      · iexists W64 0, [], [], r, rest
        iframe
        isplitr
        · simp only [insertAll, List.foldl_nil, valsOwn]; itrivial
        ipureintro; exact ⟨by word, List.nodup_nil, rfl⟩
      wp_for HI
      wp_if_destruct
      · icases restOf_open $$ Hrc with ⟨Hrc, Hrcback⟩
        wp_apply wp_rpcDec_swift_CommandId $$ Hrc as %x %r2 %ok2 Hpost
        unfold decPost
        icases Hpost with (⟨%H2, Hrc⟩ | ⟨%x', %rest2, %H2, %Hown, Hrest2⟩)
        · obtain ⟨H2, rfl⟩ := H2
          wp_auto
          wp_for_post
          ihave Hb := Hrcback $$ Hrc
          iapply HΦ; ileft; iframe Hb; ipureintro
          refine ⟨?_, rfl⟩
          simp only [pMap, pList, H, ite_eq_left hn]
          rw [pRep_none_le _ (uint.nat i + 1) _ _ _ (by word)]
          rw [pRep_succ, Hi.2.2]; simp [pEntry, H2]
        obtain ⟨H2, rfl⟩ := H2
        subst Hown
        icases restOf_open $$ Hrest2 with ⟨Hr2, Hback2⟩
        wp_auto
        wp_apply wp_rpcDec_swift_Dep $$ Hr2 as %y %r3 %ok3 Hpost
        unfold decPost
        icases Hpost with (⟨%H3, Hr2⟩ | ⟨%y', %rest3, %H3, Hown, Hrest3⟩)
        · obtain ⟨H3, rfl⟩ := H3
          wp_auto
          wp_for_post
          ihave Hrc := Hback2 $$ Hr2
          ihave Hb := Hrcback $$ Hrc
          iapply HΦ; ileft; iframe Hb; ipureintro
          refine ⟨?_, rfl⟩
          simp only [pMap, pList, H, ite_eq_left hn]
          rw [pRep_none_le _ (uint.nat i + 1) _ _ _ (by word)]
          rw [pRep_succ, Hi.2.2]; simp [pEntry, H2, H3]
        obtain ⟨H3, rfl⟩ := H3
        ihave Hrest3 := restOf_comp $$ Hback2 Hrest3
        ihave Hrc := restOf_comp $$ Hrcback Hrest3
        wp_auto
        wp_apply wp_rawMapInsert $$ Hm as Hm
        ihave Hvals := valsOwn_insert ownSliceOf x y y' gs (insertAll es) $$ [Hvals Hown]
        · iframe
        wp_for_post
        iframe
        iexists i + W64 1, es ++ [(x, y')], map.insertL x y gs, r3, rest3
        rw [insertAll_snoc]
        iframe
        ipureintro
        refine ⟨by word, map.nodup_insertL _ _ _ Hi.2.1, ?_⟩
        rw [show uint.nat (i + W64 1) = uint.nat i + 1 by word, pRep_succ, Hi.2.2]
        simp [pEntry, H2, H3]
      · have hin : i = n := by word
        subst hin
        iapply HΦ; iright; iexists insertAll es, restc
        iframe Hrc
        isplitr
        · ipureintro; refine ⟨?_, rfl⟩
          simp only [pMap, pList, H, ite_eq_left hn, Hi.2.2]
        unfold ownMapOf
        iexists gs
        iframe
        ipureintro; exact Hi.2.1

end wps

end Perennial.github_com.imdea_software.swiftpaxos.examples.swiftnet

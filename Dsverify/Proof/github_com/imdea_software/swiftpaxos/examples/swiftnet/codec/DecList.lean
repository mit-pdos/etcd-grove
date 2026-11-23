/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swiftnet/codec/DecList.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
The codec's decoders of slices (`rpcDec_S_string`, `rpcDec_S_bool`, `rpcDec_S_swift_CommandId`,
`rpcDec_S_byte`) meet their parsers.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.codec.Prim

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos.examples.swiftnet

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section wps
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics] [package_sem : examples.swiftnet.Assumptions]

/-- A decoded slice of values without heap parts: a fresh slice holding them. -/
def ownSliceOf {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] (v : GoSlice) (xs : List V) :
    IProp GF := iprop(v ↦* xs)

theorem wp_rpcDec_S_string (b : GoSlice) (dq : DFrac) (bs : List w8) :
    {{ (b ↦*{dq} bs : IProp GF) }}
      (App (Val (@! rpcDec_S_string)) (Val #b))
    {{ (v : GoSlice) (r : GoSlice) (ok : Bool), RET (PairV (PairV #v #r) #ok);
        decPost (pList pBytes) ownSliceOf b dq bs v r ok }} := by
  wp_start as Hb
  wp_auto
  wp_apply wp_rpcGetU64 $$ Hb as %n %r %ok Hpost
  unfold decPost
  icases Hpost with (⟨%H, Hb⟩ | ⟨%a, %rest, %H, %Hown, Hrest⟩)
  · obtain ⟨H, rfl⟩ := H
    wp_auto
    iapply HΦ; ileft; iframe Hb; ipureintro; exact ⟨by simp [pList, H], rfl⟩
  · obtain ⟨H, rfl⟩ := H
    subst Hown
    icases restOf_open $$ Hrest with ⟨Hr, Hback⟩
    ihave %Hrl := ownSlice_len _ _ _ $$ Hr
    wp_auto
    wp_if_destruct
    · ihave Hb := Hback $$ Hr
      iapply HΦ; ileft; iframe Hb; ipureintro
      refine ⟨?_, rfl⟩
      simp only [pList, H]; rw [ite_eq_right_iff]; intro h; exfalso; word
    · have hn : uint.nat n ≤ rest.length := by word
      ihave Hrc := restOf_close $$ [Hr Hback]
      · iframe Hr Hback
      ihave HI : (∃ (i : w64) (xs : List GoString) (vs rc : GoSlice) (restc : List w8),
          "i" ∷ i_ptr ↦ i ∗ "v" ∷ v_ptr ↦ vs ∗ "Hvs" ∷ vs ↦* xs ∗
          "Hcap" ∷ ownSliceCap GoString vs (DFrac.own 1) ∗
          "r" ∷ r_ptr ↦ rc ∗ "Hrc" ∷ restOf b dq bs rc restc ∗
          "%Hi" ∷ ⌜uint.nat i ≤ uint.nat n ∧ pRep pBytes (uint.nat i) rest = some (xs, restc)⌝ :
          IProp GF) $$ [i v r Hrc]
      · iexists W64 0, [], zero_val GoSlice, r, rest
        iframe
        isplitr
        · iapply ownSlice_nil
        isplitr
        · iapply ownSliceCap_nil
        ipureintro; exact ⟨by word, rfl⟩
      wp_for HI
      wp_if_destruct
      · icases restOf_open $$ Hrc with ⟨Hrc, Hrcback⟩
        wp_apply wp_rpcDec_string $$ Hrc as %x %r2 %ok2 Hpost
        unfold decPost
        icases Hpost with (⟨%H2, Hrc⟩ | ⟨%a, %rest2, %H2, %Hown, Hrest2⟩)
        · obtain ⟨H2, rfl⟩ := H2
          wp_auto
          wp_for_post
          ihave Hb := Hrcback $$ Hrc
          iapply HΦ; ileft; iframe Hb; ipureintro
          refine ⟨?_, rfl⟩
          simp only [pList, H, ite_eq_left hn]
          apply pRep_none_le _ (uint.nat i + 1) _ _ _ (by word)
          rw [pRep_succ, Hi.2]; simp [H2]
        · obtain ⟨H2, rfl⟩ := H2
          subst Hown
          wp_auto
          wp_apply wp_slice_literal (V := GoString) (t := go.string) [x]
          isplitr
          · ipureintro; rfl
          iintro %sl ⟨Hsl, -⟩
          wp_auto
          wp_apply wp_slice_append $$ [Hvs Hcap Hsl] as %vs' ⟨Hvs, Hcap, -⟩
          · iframe
          wp_auto
          wp_for_post
          ihave Hrc := restOf_comp b dq bs rc restc r2 rest2 $$ Hrcback Hrest2
          iframe
          iexists i + W64 1, xs ++ [x], vs', r2, rest2
          iframe
          ipureintro
          refine ⟨by word, ?_⟩
          rw [show uint.nat (i + W64 1) = uint.nat i + 1 by word, pRep_succ, Hi.2]
          simp [H2]
      · have hin : i = n := by word
        subst hin
        iapply HΦ; iright; iexists xs, restc
        iframe Hrc
        isplitr
        · ipureintro; refine ⟨?_, rfl⟩
          simp only [pList, H, ite_eq_left hn]; exact Hi.2
        unfold ownSliceOf; iexact Hvs

theorem wp_rpcDec_S_bool (b : GoSlice) (dq : DFrac) (bs : List w8) :
    {{ (b ↦*{dq} bs : IProp GF) }}
      (App (Val (@! rpcDec_S_bool)) (Val #b))
    {{ (v : GoSlice) (r : GoSlice) (ok : Bool), RET (PairV (PairV #v #r) #ok);
        decPost (pList pBool) ownSliceOf b dq bs v r ok }} := by
  wp_start as Hb
  wp_auto
  wp_apply wp_rpcGetU64 $$ Hb as %n %r %ok Hpost
  unfold decPost
  icases Hpost with (⟨%H, Hb⟩ | ⟨%a, %rest, %H, %Hown, Hrest⟩)
  · obtain ⟨H, rfl⟩ := H
    wp_auto
    iapply HΦ; ileft; iframe Hb; ipureintro; exact ⟨by simp [pList, H], rfl⟩
  · obtain ⟨H, rfl⟩ := H
    subst Hown
    icases restOf_open $$ Hrest with ⟨Hr, Hback⟩
    ihave %Hrl := ownSlice_len _ _ _ $$ Hr
    wp_auto
    wp_if_destruct
    · ihave Hb := Hback $$ Hr
      iapply HΦ; ileft; iframe Hb; ipureintro
      refine ⟨?_, rfl⟩
      simp only [pList, H]; rw [ite_eq_right_iff]; intro h; exfalso; word
    · have hn : uint.nat n ≤ rest.length := by word
      ihave Hrc := restOf_close $$ [Hr Hback]
      · iframe Hr Hback
      ihave HI : (∃ (i : w64) (xs : List Bool) (vs rc : GoSlice) (restc : List w8),
          "i" ∷ i_ptr ↦ i ∗ "v" ∷ v_ptr ↦ vs ∗ "Hvs" ∷ vs ↦* xs ∗
          "Hcap" ∷ ownSliceCap Bool vs (DFrac.own 1) ∗
          "r" ∷ r_ptr ↦ rc ∗ "Hrc" ∷ restOf b dq bs rc restc ∗
          "%Hi" ∷ ⌜uint.nat i ≤ uint.nat n ∧ pRep pBool (uint.nat i) rest = some (xs, restc)⌝ :
          IProp GF) $$ [i v r Hrc]
      · iexists W64 0, [], zero_val GoSlice, r, rest
        iframe
        isplitr
        · iapply ownSlice_nil
        isplitr
        · iapply ownSliceCap_nil
        ipureintro; exact ⟨by word, rfl⟩
      wp_for HI
      wp_if_destruct
      · icases restOf_open $$ Hrc with ⟨Hrc, Hrcback⟩
        wp_apply wp_rpcDec_bool $$ Hrc as %x %r2 %ok2 Hpost
        unfold decPost
        icases Hpost with (⟨%H2, Hrc⟩ | ⟨%a, %rest2, %H2, %Hown, Hrest2⟩)
        · obtain ⟨H2, rfl⟩ := H2
          wp_auto
          wp_for_post
          ihave Hb := Hrcback $$ Hrc
          iapply HΦ; ileft; iframe Hb; ipureintro
          refine ⟨?_, rfl⟩
          simp only [pList, H, ite_eq_left hn]
          apply pRep_none_le _ (uint.nat i + 1) _ _ _ (by word)
          rw [pRep_succ, Hi.2]; simp [H2]
        · obtain ⟨H2, rfl⟩ := H2
          subst Hown
          wp_auto
          wp_apply wp_slice_literal (V := Bool) (t := go.bool) [x]
          isplitr
          · ipureintro; rfl
          iintro %sl ⟨Hsl, -⟩
          wp_auto
          wp_apply wp_slice_append $$ [Hvs Hcap Hsl] as %vs' ⟨Hvs, Hcap, -⟩
          · iframe
          wp_auto
          wp_for_post
          ihave Hrc := restOf_comp b dq bs rc restc r2 rest2 $$ Hrcback Hrest2
          iframe
          iexists i + W64 1, xs ++ [x], vs', r2, rest2
          iframe
          ipureintro
          refine ⟨by word, ?_⟩
          rw [show uint.nat (i + W64 1) = uint.nat i + 1 by word, pRep_succ, Hi.2]
          simp [H2]
      · have hin : i = n := by word
        subst hin
        iapply HΦ; iright; iexists xs, restc
        iframe Hrc
        isplitr
        · ipureintro; refine ⟨?_, rfl⟩
          simp only [pList, H, ite_eq_left hn]; exact Hi.2
        unfold ownSliceOf; iexact Hvs

theorem wp_rpcDec_S_swift_CommandId (b : GoSlice) (dq : DFrac) (bs : List w8) :
    {{ (b ↦*{dq} bs : IProp GF) }}
      (App (Val (@! rpcDec_S_swift_CommandId)) (Val #b))
    {{ (v : GoSlice) (r : GoSlice) (ok : Bool), RET (PairV (PairV #v #r) #ok);
        decPost (pList pCmdId) ownSliceOf b dq bs v r ok }} := by
  wp_start as Hb
  wp_auto
  wp_apply wp_rpcGetU64 $$ Hb as %n %r %ok Hpost
  unfold decPost
  icases Hpost with (⟨%H, Hb⟩ | ⟨%a, %rest, %H, %Hown, Hrest⟩)
  · obtain ⟨H, rfl⟩ := H
    wp_auto
    iapply HΦ; ileft; iframe Hb; ipureintro; exact ⟨by simp [pList, H], rfl⟩
  · obtain ⟨H, rfl⟩ := H
    subst Hown
    icases restOf_open $$ Hrest with ⟨Hr, Hback⟩
    ihave %Hrl := ownSlice_len _ _ _ $$ Hr
    wp_auto
    wp_if_destruct
    · ihave Hb := Hback $$ Hr
      iapply HΦ; ileft; iframe Hb; ipureintro
      refine ⟨?_, rfl⟩
      simp only [pList, H]; rw [ite_eq_right_iff]; intro h; exfalso; word
    · have hn : uint.nat n ≤ rest.length := by word
      ihave Hrc := restOf_close $$ [Hr Hback]
      · iframe Hr Hback
      ihave HI : (∃ (i : w64) (xs : List swift.CommandId) (vs rc : GoSlice) (restc : List w8),
          "i" ∷ i_ptr ↦ i ∗ "v" ∷ v_ptr ↦ vs ∗ "Hvs" ∷ vs ↦* xs ∗
          "Hcap" ∷ ownSliceCap swift.CommandId vs (DFrac.own 1) ∗
          "r" ∷ r_ptr ↦ rc ∗ "Hrc" ∷ restOf b dq bs rc restc ∗
          "%Hi" ∷ ⌜uint.nat i ≤ uint.nat n ∧ pRep pCmdId (uint.nat i) rest = some (xs, restc)⌝ :
          IProp GF) $$ [i v r Hrc]
      · iexists W64 0, [], zero_val GoSlice, r, rest
        iframe
        isplitr
        · iapply ownSlice_nil
        isplitr
        · iapply ownSliceCap_nil
        ipureintro; exact ⟨by word, rfl⟩
      wp_for HI
      wp_if_destruct
      · icases restOf_open $$ Hrc with ⟨Hrc, Hrcback⟩
        wp_apply wp_rpcDec_swift_CommandId $$ Hrc as %x %r2 %ok2 Hpost
        unfold decPost
        icases Hpost with (⟨%H2, Hrc⟩ | ⟨%a, %rest2, %H2, %Hown, Hrest2⟩)
        · obtain ⟨H2, rfl⟩ := H2
          wp_auto
          wp_for_post
          ihave Hb := Hrcback $$ Hrc
          iapply HΦ; ileft; iframe Hb; ipureintro
          refine ⟨?_, rfl⟩
          simp only [pList, H, ite_eq_left hn]
          apply pRep_none_le _ (uint.nat i + 1) _ _ _ (by word)
          rw [pRep_succ, Hi.2]; simp [H2]
        · obtain ⟨H2, rfl⟩ := H2
          subst Hown
          wp_auto
          wp_apply wp_slice_literal (V := swift.CommandId) (t := swift.CommandId.ty) [x]
          isplitr
          · ipureintro; rfl
          iintro %sl ⟨Hsl, -⟩
          wp_auto
          wp_apply wp_slice_append $$ [Hvs Hcap Hsl] as %vs' ⟨Hvs, Hcap, -⟩
          · iframe
          wp_auto
          wp_for_post
          ihave Hrc := restOf_comp b dq bs rc restc r2 rest2 $$ Hrcback Hrest2
          iframe
          iexists i + W64 1, xs ++ [x], vs', r2, rest2
          iframe
          ipureintro
          refine ⟨by word, ?_⟩
          rw [show uint.nat (i + W64 1) = uint.nat i + 1 by word, pRep_succ, Hi.2]
          simp [H2]
      · have hin : i = n := by word
        subst hin
        iapply HΦ; iright; iexists xs, restc
        iframe Hrc
        isplitr
        · ipureintro; refine ⟨?_, rfl⟩
          simp only [pList, H, ite_eq_left hn]; exact Hi.2
        unfold ownSliceOf; iexact Hvs

end wps

end Perennial.github_com.imdea_software.swiftpaxos.examples.swiftnet

namespace Perennial.github_com.imdea_software.swiftpaxos.examples.swiftnet
open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
section wps2
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics] [package_sem : examples.swiftnet.Assumptions]

theorem wp_rpcDec_S_byte (b : GoSlice) (dq : DFrac) (bs : List w8) :
    {{ (b ↦*{dq} bs : IProp GF) }}
      (App (Val (@! rpcDec_S_byte)) (Val #b))
    {{ (v : GoSlice) (r : GoSlice) (ok : Bool), RET (PairV (PairV #v #r) #ok);
        decPost pBytes ownSliceOf b dq bs v r ok }} := by
  wp_start as Hb
  wp_auto
  wp_apply wp_rpcGetU64 $$ Hb as %n %r %ok Hpost
  unfold decPost
  icases Hpost with (⟨%H, Hb⟩ | ⟨%a, %rest, %H, %Hown, Hrest⟩)
  · obtain ⟨H, rfl⟩ := H
    wp_auto
    iapply HΦ; ileft; iframe Hb; ipureintro; exact ⟨by simp [pBytes, H], rfl⟩
  · obtain ⟨H, rfl⟩ := H
    subst Hown
    icases restOf_open $$ Hrest with ⟨Hr, Hback⟩
    ihave %Hrl := ownSlice_len _ _ _ $$ Hr
    ihave %Hrwf := ownSlice_wf _ _ _ $$ Hr
    wp_auto
    wp_if_destruct
    · ihave Hb := Hback $$ Hr
      iapply HΦ; ileft; iframe Hb; ipureintro
      refine ⟨?_, rfl⟩
      simp only [pBytes, H]; rw [ite_eq_right_iff]; intro h; exfalso; word
    · have hx : uint.nat n ≤ rest.length := by word
      wp_if_destruct
      · ihave Hrest := restOf_close $$ [Hr Hback]
        · iframe
        iapply HΦ; iright; iexists [], rest
        iframe Hrest
        isplitr
        · ipureintro; refine ⟨?_, rfl⟩
          simp only [pBytes, H, ite_eq_left hx]; simp
        unfold ownSliceOf; iapply ownSlice_nil
      · wp_apply (wp_slice_make2 (V := w8) n) as %v ⟨Hv, -⟩
        · ipureintro; word
        rw [ite_eq_left (by word)]
        ihave ⟨Hsub, Hsubback⟩ := take_acc r dq rest n hx $$ Hr
        wp_apply wp_slice_copy $$ [Hv Hsub] as %k ⟨%Hk, Hv, Hsub⟩
        · iframe
        ihave Hr := Hsubback $$ Hsub
        wp_auto
        rw [ite_eq_left (by word)]
        ihave Hrest := restOf_drop r dq rest n hx $$ Hr
        ihave Hrest := restOf_comp $$ Hback Hrest
        wp_auto
        iapply HΦ; iright; iexists (rest.take (uint.nat n)), (rest.drop (uint.nat n))
        iframe Hrest
        isplitr
        · ipureintro; refine ⟨?_, rfl⟩
          simp only [pBytes, H, ite_eq_left hx]
        unfold ownSliceOf
        have e : List.take (List.replicate (sint.nat n) (zero_val w8)).length
            (List.take (uint.nat n) rest) ++
            List.drop (List.take (uint.nat n) rest).length (List.replicate (sint.nat n) (zero_val w8)) =
            List.take (uint.nat n) rest := by
          have h1 : sint.nat n = uint.nat n := by word
          rw [List.length_replicate, h1, List.take_of_length_le (by simp; omega)]
          rw [List.length_take, Nat.min_eq_left hx, List.drop_replicate, Nat.sub_self,
            List.replicate_zero, List.append_nil]
        rw [e]
        iexact Hv
end wps2
end Perennial.github_com.imdea_software.swiftpaxos.examples.swiftnet

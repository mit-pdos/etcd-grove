/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swiftnet/codec/Prim.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
module

public import Dsverify.GeneratedProof.github_com.imdea_software.swiftpaxos.examples.swiftnet
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.codec.Base

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

theorem wp_rpcPutU64 (b : GoSlice) (bs : List w8) (x : w64) :
    {{ (b ↦* bs ∗ ownSliceCap w8 b (DFrac.own 1) : IProp GF) }}
      (App (App (Val (@! rpcPutU64)) (Val #b)) (Val #x))
    {{ (b' : GoSlice), RET #b'; b' ↦* (bs ++ u64Le x) ∗ ownSliceCap w8 b' (DFrac.own 1) }} := by
  wp_start as ⟨Hb, Hcap⟩
  wp_auto
  wp_apply wp_slice_literal (V := w8) (t := go.byte)
    [W8 (uint.Z x), W8 (uint.Z (x >>> W64 8)), W8 (uint.Z (x >>> W64 16)),
     W8 (uint.Z (x >>> W64 24)), W8 (uint.Z (x >>> W64 32)), W8 (uint.Z (x >>> W64 40)),
     W8 (uint.Z (x >>> W64 48)), W8 (uint.Z (x >>> W64 56))]
  isplitr
  · ipureintro; rfl
  iintro %sl ⟨Hsl, -⟩
  wp_auto
  wp_apply wp_slice_append $$ [Hb Hcap Hsl] as %b' ⟨Hb, Hcap, -⟩
  · iframe
  have : [W8 (uint.Z x), W8 (uint.Z (x >>> W64 8)), W8 (uint.Z (x >>> W64 16)),
     W8 (uint.Z (x >>> W64 24)), W8 (uint.Z (x >>> W64 32)), W8 (uint.Z (x >>> W64 40)),
     W8 (uint.Z (x >>> W64 48)), W8 (uint.Z (x >>> W64 56))] = u64Le x := u64Le_bytes x
  rw [this]
  wp_end


theorem wp_rpcGetU64 (b : GoSlice) (dq : DFrac) (bs : List w8) :
    {{ (b ↦*{dq} bs : IProp GF) }}
      (App (Val (@! rpcGetU64)) (Val #b))
    {{ (x : w64) (r : GoSlice) (ok : Bool), RET (PairV (PairV #x #r) #ok);
        decPost pU64 ownPure b dq bs x r ok }} := by
  wp_start as Hb
  ihave %Hlen := ownSlice_len _ _ _ $$ Hb
  ihave %Hwf := ownSlice_wf _ _ _ $$ Hb
  wp_auto
  wp_if_destruct
  · have : pU64 bs = none := by
      unfold pU64; rw [ite_eq_right_iff]; intro h; exfalso; word
    iapply HΦ
    unfold decPost
    ileft
    iframe Hb
    ipureintro; exact ⟨this, rfl⟩
  · obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, rest, rfl⟩ : ∃ b0 b1 b2 b3 b4 b5 b6 b7 rest,
        bs = [b0, b1, b2, b3, b4, b5, b6, b7] ++ rest := by
      match bs, Hlen with
      | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: rest, _ =>
        exact ⟨b0, b1, b2, b3, b4, b5, b6, b7, rest, rfl⟩
      | [], h | [_], h | [_, _], h | [_, _, _], h | [_, _, _, _], h | [_, _, _, _, _], h
      | [_, _, _, _, _, _], h | [_, _, _, _, _, _, _], h => simp at h; word
    rw [ite_eq_left (by word)]
    wp_apply (wp_load_slice_index b (sint.Z (W64 0)) _ dq b0 (by decide)) $$ [Hb] as Hb
    · iframe; ipureintro; rfl
    rw [ite_eq_left (by word)]
    wp_apply (wp_load_slice_index b (sint.Z (W64 1)) _ dq b1 (by decide)) $$ [Hb] as Hb
    · iframe; ipureintro; rfl
    rw [ite_eq_left (by word)]
    wp_apply (wp_load_slice_index b (sint.Z (W64 2)) _ dq b2 (by decide)) $$ [Hb] as Hb
    · iframe; ipureintro; rfl
    rw [ite_eq_left (by word)]
    wp_apply (wp_load_slice_index b (sint.Z (W64 3)) _ dq b3 (by decide)) $$ [Hb] as Hb
    · iframe; ipureintro; rfl
    rw [ite_eq_left (by word)]
    wp_apply (wp_load_slice_index b (sint.Z (W64 4)) _ dq b4 (by decide)) $$ [Hb] as Hb
    · iframe; ipureintro; rfl
    rw [ite_eq_left (by word)]
    wp_apply (wp_load_slice_index b (sint.Z (W64 5)) _ dq b5 (by decide)) $$ [Hb] as Hb
    · iframe; ipureintro; rfl
    rw [ite_eq_left (by word)]
    wp_apply (wp_load_slice_index b (sint.Z (W64 6)) _ dq b6 (by decide)) $$ [Hb] as Hb
    · iframe; ipureintro; rfl
    rw [ite_eq_left (by word)]
    wp_apply (wp_load_slice_index b (sint.Z (W64 7)) _ dq b7 (by decide)) $$ [Hb] as Hb
    · iframe; ipureintro; rfl
    wp_pures
    rw [leToU64_or]
    wp_auto
    rw [ite_eq_left (by word)]
    ihave ⟨%Hsz, Hsuf, Hback⟩ := net.rpc.ownSlice_drop_acc b dq [b0, b1, b2, b3, b4, b5, b6, b7] rest $$ Hb
    wp_auto
    have : pU64 ([b0, b1, b2, b3, b4, b5, b6, b7] ++ rest) =
        some (leToU64 [b0, b1, b2, b3, b4, b5, b6, b7], rest) := by
      simp [pU64]
    iapply HΦ
    unfold decPost
    iright
    iexists _, rest
    isplitr
    · ipureintro; exact ⟨this, rfl⟩
    isplitr
    · unfold ownPure; ipureintro; rfl
    unfold restOf
    iframe Hsuf
    iintro Hsuf
    iapply Hback $$ %rest %rfl Hsuf
end wps
end Perennial.github_com.imdea_software.swiftpaxos.examples.swiftnet

namespace Perennial.github_com.imdea_software.swiftpaxos.examples.swiftnet
open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
section wps3

variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics] [package_sem : examples.swiftnet.Assumptions]

theorem wp_rpcDec_int (b : GoSlice) (dq : DFrac) (bs : List w8) :
    {{ (b ↦*{dq} bs : IProp GF) }}
      (App (Val (@! rpcDec_int)) (Val #b))
    {{ (x : w64) (r : GoSlice) (ok : Bool), RET (PairV (PairV #x #r) #ok);
        decPost pInt ownPure b dq bs x r ok }} := by
  wp_start as Hb
  wp_auto
  wp_apply wp_rpcGetU64 $$ Hb as %x %r %ok Hpost
  unfold decPost
  icases Hpost with (⟨%H, Hb⟩ | ⟨%a, %rest, %H, %Hown, Hrest⟩)
  · obtain ⟨H, rfl⟩ := H
    wp_auto
    iapply HΦ; ileft; iframe Hb; ipureintro; exact ⟨H, rfl⟩
  · obtain ⟨H, rfl⟩ := H
    subst Hown
    wp_auto
    iapply HΦ; iright; iexists _, rest; iframe Hrest; ipureintro; exact ⟨⟨H, rfl⟩, rfl⟩

theorem wp_rpcDec_uint8 (b : GoSlice) (dq : DFrac) (bs : List w8) :
    {{ (b ↦*{dq} bs : IProp GF) }}
      (App (Val (@! rpcDec_uint8)) (Val #b))
    {{ (x : w8) (r : GoSlice) (ok : Bool), RET (PairV (PairV #x #r) #ok);
        decPost pU8 ownPure b dq bs x r ok }} := by
  wp_start as Hb
  wp_auto
  wp_apply wp_rpcGetU64 $$ Hb as %x %r %ok Hpost
  unfold decPost
  icases Hpost with (⟨%H, Hb⟩ | ⟨%a, %rest, %H, %Hown, Hrest⟩)
  · obtain ⟨H, rfl⟩ := H
    wp_auto
    iapply HΦ; ileft; iframe Hb; ipureintro; exact ⟨by simp [pU8, H], rfl⟩
  · obtain ⟨H, rfl⟩ := H
    subst Hown
    wp_auto
    wp_if_destruct
    · iapply HΦ; iright; iexists _, rest; iframe Hrest; ipureintro
      refine ⟨⟨?_, rfl⟩, rfl⟩
      simp only [pU8, H]; rw [ite_eq_left (by word)]
    · ihave Hb := restOf_back $$ Hrest
      iapply HΦ; ileft; iframe Hb; ipureintro
      refine ⟨?_, rfl⟩
      simp only [pU8, H]; rw [ite_eq_right_iff]; intro h; exfalso; word

theorem wp_rpcDec_int32 (b : GoSlice) (dq : DFrac) (bs : List w8) :
    {{ (b ↦*{dq} bs : IProp GF) }}
      (App (Val (@! rpcDec_int32)) (Val #b))
    {{ (x : w32) (r : GoSlice) (ok : Bool), RET (PairV (PairV #x #r) #ok);
        decPost pI32 ownPure b dq bs x r ok }} := by
  wp_start as Hb
  wp_auto
  wp_apply wp_rpcGetU64 $$ Hb as %x %r %ok Hpost
  unfold decPost
  icases Hpost with (⟨%H, Hb⟩ | ⟨%a, %rest, %H, %Hown, Hrest⟩)
  · obtain ⟨H, rfl⟩ := H
    wp_auto
    iapply HΦ; ileft; iframe Hb; ipureintro; exact ⟨by simp [pI32, H], rfl⟩
  · obtain ⟨H, rfl⟩ := H
    subst Hown
    wp_auto
    wp_if_destruct
    · wp_if_destruct
      · iapply HΦ; iright; iexists _, rest; iframe Hrest; ipureintro
        refine ⟨⟨?_, rfl⟩, rfl⟩
        simp only [pI32, H]; rw [ite_eq_left (by word)]
      · ihave Hb := restOf_back $$ Hrest
        iapply HΦ; ileft; iframe Hb; ipureintro
        refine ⟨?_, rfl⟩
        simp only [pI32, H]; rw [ite_eq_right_iff]; intro h; exfalso; word
    · ihave Hb := restOf_back $$ Hrest
      iapply HΦ; ileft; iframe Hb; ipureintro
      refine ⟨?_, rfl⟩
      simp only [pI32, H]; rw [ite_eq_right_iff]; intro h; exfalso; word

theorem wp_rpcDec_int64 (b : GoSlice) (dq : DFrac) (bs : List w8) :
    {{ (b ↦*{dq} bs : IProp GF) }}
      (App (Val (@! rpcDec_int64)) (Val #b))
    {{ (x : w64) (r : GoSlice) (ok : Bool), RET (PairV (PairV #x #r) #ok);
        decPost pInt ownPure b dq bs x r ok }} := by
  wp_start as Hb
  wp_auto
  wp_apply wp_rpcGetU64 $$ Hb as %x %r %ok Hpost
  unfold decPost
  icases Hpost with (⟨%H, Hb⟩ | ⟨%a, %rest, %H, %Hown, Hrest⟩)
  · obtain ⟨H, rfl⟩ := H
    wp_auto
    iapply HΦ; ileft; iframe Hb; ipureintro; exact ⟨H, rfl⟩
  · obtain ⟨H, rfl⟩ := H
    subst Hown
    wp_auto
    iapply HΦ; iright; iexists _, rest; iframe Hrest; ipureintro; exact ⟨⟨H, rfl⟩, rfl⟩

theorem wp_rpcDec_bool (b : GoSlice) (dq : DFrac) (bs : List w8) :
    {{ (b ↦*{dq} bs : IProp GF) }}
      (App (Val (@! rpcDec_bool)) (Val #b))
    {{ (x : Bool) (r : GoSlice) (ok : Bool), RET (PairV (PairV #x #r) #ok);
        decPost pBool ownPure b dq bs x r ok }} := by
  wp_start as Hb
  ihave %Hlen := ownSlice_len _ _ _ $$ Hb
  ihave %Hwf := ownSlice_wf _ _ _ $$ Hb
  wp_auto
  rcases bs with _ | ⟨b0, rest⟩
  · rw [show decide (sint.Z b.len < sint.Z (W64 1)) = true by simp at Hlen; simp; word]
    wp_auto
    iapply HΦ; unfold decPost; ileft; iframe Hb; ipureintro; exact ⟨rfl, rfl⟩
  · rw [show decide (sint.Z b.len < sint.Z (W64 1)) = false by simp at Hlen; simp; word]
    wp_auto
    rw [ite_eq_left (by simp at Hlen; word)]
    wp_apply (wp_load_slice_index b (sint.Z (W64 0)) _ dq b0 (by decide)) $$ [Hb] as Hb
    · iframe; ipureintro; rfl
    wp_if_destruct
    · iapply HΦ; unfold decPost; ileft; iframe Hb; ipureintro
      refine ⟨?_, rfl⟩
      simp only [pBool]; rw [ite_eq_right_iff]; intro h; exfalso; word
    · rw [ite_eq_left (by simp at Hlen; word)]
      wp_apply (wp_load_slice_index b (sint.Z (W64 0)) _ dq b0 (by decide)) $$ [Hb] as Hb
      · iframe; ipureintro; rfl
      wp_pures
      wp_auto
      rw [ite_eq_left (by simp at Hlen; word)]
      ihave Hrest := restOf_drop' b dq (b0 :: rest) (W64 1) rest (by simp <;> word) rfl $$ Hb
      wp_auto
      iapply HΦ; unfold decPost; iright; iexists _, _
      isplitr
      · ipureintro
        refine ⟨?_, rfl⟩
        simp only [pBool]; rw [ite_eq_left (by word)]
      isplitr
      · ipureintro; rfl
      iexact Hrest

theorem wp_rpcDec_string (b : GoSlice) (dq : DFrac) (bs : List w8) :
    {{ (b ↦*{dq} bs : IProp GF) }}
      (App (Val (@! rpcDec_string)) (Val #b))
    {{ (x : GoString) (r : GoSlice) (ok : Bool), RET (PairV (PairV #x #r) #ok);
        decPost pBytes ownPure b dq bs x r ok }} := by
  wp_start as Hb
  wp_auto
  wp_apply wp_rpcGetU64 $$ Hb as %x %r %ok Hpost
  unfold decPost
  icases Hpost with (⟨%H, Hb⟩ | ⟨%a, %rest, %H, %Hown, Hrest⟩)
  · obtain ⟨H, rfl⟩ := H
    wp_auto
    iapply HΦ; ileft; iframe Hb; ipureintro; exact ⟨by simp [pBytes, H], rfl⟩
  · obtain ⟨H, rfl⟩ := H
    subst Hown
    unfold restOf; icases Hrest with ⟨Hr, Hback⟩
    ihave %Hrl := ownSlice_len _ _ _ $$ Hr
    ihave %Hrwf := ownSlice_wf _ _ _ $$ Hr
    wp_auto
    wp_if_destruct
    · ihave Hb := Hback $$ Hr
      iapply HΦ; ileft; iframe Hb; ipureintro
      refine ⟨?_, rfl⟩
      simp only [pBytes, H]; rw [ite_eq_right_iff]; intro h; exfalso; word
    · have hx : uint.nat x ≤ rest.length := by word
      rw [ite_eq_left (by word)]
      ihave ⟨Hsub, Hsubback⟩ := take_acc r dq rest x hx $$ Hr
      wp_apply wp_bytes_to_string $$ Hsub as Hsub
      ihave Hr := Hsubback $$ Hsub
      rw [ite_eq_left (by word)]
      ihave Hrest := restOf_drop r dq rest x hx $$ Hr
      wp_auto
      unfold restOf
      icases Hrest with ⟨Hr', Hb'⟩
      iapply HΦ; iright; iexists (rest.take (uint.nat x)), (rest.drop (uint.nat x))
      iframe Hr'
      isplitr
      · ipureintro
        refine ⟨?_, rfl⟩
        simp only [pBytes, H]; rw [ite_eq_left hx]
      isplitr
      · ipureintro; rfl
      iintro Hr'
      iapply Hback
      iapply Hb' $$ Hr'
end wps3
end Perennial.github_com.imdea_software.swiftpaxos.examples.swiftnet

namespace Perennial.github_com.imdea_software.swiftpaxos.examples.swiftnet
open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
section wps4

variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics] [package_sem : examples.swiftnet.Assumptions]

theorem wp_rpcDec_swift_CommandId (b : GoSlice) (dq : DFrac) (bs : List w8) :
    {{ (b ↦*{dq} bs : IProp GF) }}
      (App (Val (@! rpcDec_swift_CommandId)) (Val #b))
    {{ (x : swift.CommandId) (r : GoSlice) (ok : Bool), RET (PairV (PairV #x #r) #ok);
        decPost pCmdId ownPure b dq bs x r ok }} := by
  wp_start as Hb
  wp_auto
  wp_apply wp_rpcDec_int32 $$ Hb as %c %r0 %ok0 Hpost
  unfold decPost
  icases Hpost with (⟨%H, Hb⟩ | ⟨%c', %rest0, %H, %Hown, Hrest⟩)
  · obtain ⟨H, rfl⟩ := H
    wp_auto
    iapply HΦ; ileft; iframe Hb; ipureintro; exact ⟨by simp [pCmdId, H], rfl⟩
  · obtain ⟨H, rfl⟩ := H
    subst Hown
    icases restOf_open $$ Hrest with ⟨Hr, Hback⟩
    wp_auto
    wp_apply wp_rpcDec_int32 $$ Hr as %s %r1 %ok1 Hpost
    unfold decPost
    icases Hpost with (⟨%H1, Hr⟩ | ⟨%s', %rest1, %H1, %Hown, Hrest⟩)
    · obtain ⟨H1, rfl⟩ := H1
      ihave Hb := Hback $$ Hr
      wp_auto
      iapply HΦ; ileft; iframe Hb; ipureintro; exact ⟨by simp [pCmdId, H, H1], rfl⟩
    · obtain ⟨H1, rfl⟩ := H1
      subst Hown
      ihave Hrest := restOf_comp $$ Hback Hrest
      wp_auto
      iapply HΦ; iright; iexists _, rest1; iframe Hrest; ipureintro
      exact ⟨⟨by simp [pCmdId, H, H1], rfl⟩, rfl⟩
end wps4
end Perennial.github_com.imdea_software.swiftpaxos.examples.swiftnet

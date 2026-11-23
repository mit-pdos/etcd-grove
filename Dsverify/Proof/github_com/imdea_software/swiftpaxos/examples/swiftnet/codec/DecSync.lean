/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swiftnet/codec/DecSync.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
The codec's decoder of `swift.MSync` (`rpcDec_swift_MSync`) meets its parser.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.codec.DecMap

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

/-- A decoded optional map: nil, or a fresh map holding the entries. -/
def optMapOwn {G A : Type} [ZeroVal G] (own : G → A → IProp GF) (mp : GoMap) :
    Option (List (swift.CommandId × A)) → IProp GF
  | none => iprop(⌜mp = map.nil⌝)
  | some l => ownMapOf own mp l

/-- A decoded `MSync`. -/
def ownSync (m : swift.MSync) (sv : SyncVal) : IProp GF :=
  iprop(⌜m.Replica' = sv.rep ∧ m.Ballot' = sv.bal⌝ ∗ optMapOwn ownPure m.Phases' sv.phases ∗
    optMapOwn ownCmd m.Cmds' sv.cmds ∗ optMapOwn ownSliceOf m.Deps' sv.deps)

theorem wp_rpcDec_swift_MSync (b : GoSlice) (dq : DFrac) (bs : List w8) :
    {{ (b ↦*{dq} bs : IProp GF) }}
      (App (Val (@! rpcDec_swift_MSync)) (Val #b))
    {{ (m : swift.MSync) (r : GoSlice) (ok : Bool), RET (PairV (PairV #m #r) #ok);
        decPost pMSync ownSync b dq bs m r ok }} := by
  wp_start as Hb
  wp_auto
  wp_apply wp_rpcDec_int32 $$ Hb as %rep %r0 %ok0 Hpost
  unfold decPost
  icases Hpost with (⟨%H, Hb⟩ | ⟨%rep', %rest0, %H, %Hown, Hrest⟩)
  · obtain ⟨H, rfl⟩ := H
    wp_auto
    iapply HΦ; ileft; iframe Hb; ipureintro; exact ⟨by simp [pMSync, H], rfl⟩
  obtain ⟨H, rfl⟩ := H
  subst Hown
  icases restOf_open $$ Hrest with ⟨Hr, Hback⟩
  wp_auto
  wp_apply wp_rpcDec_int32 $$ Hr as %bal %r1 %ok1 Hpost
  unfold decPost
  icases Hpost with (⟨%H1, Hr⟩ | ⟨%bal', %rest1, %H1, %Hown, Hrest⟩)
  · obtain ⟨H1, rfl⟩ := H1
    ihave Hb := Hback $$ Hr
    wp_auto
    iapply HΦ; ileft; iframe Hb; ipureintro; exact ⟨by simp [pMSync, H, H1], rfl⟩
  obtain ⟨H1, rfl⟩ := H1
  subst Hown
  ihave Hrest := restOf_comp $$ Hback Hrest
  icases restOf_open $$ Hrest with ⟨Hr, Hback⟩
  ihave %Hrl := ownSlice_len _ _ _ $$ Hr
  ihave %Hrwf := ownSlice_wf _ _ _ $$ Hr
  wp_auto
  rcases hR : rest1 with _ | ⟨c, rest1'⟩
  · subst hR
    rw [show decide (sint.Z (W64 0) < sint.Z r1.len) = false by simp at Hrl; simp; word]
    wp_auto
    ihave Hb := Hback $$ Hr
    iapply HΦ; ileft; iframe Hb; ipureintro
    refine ⟨?_, rfl⟩
    simp only [pMSync, H, H1]; simp [pOpt]
  subst hR
  rw [show decide (sint.Z (W64 0) < sint.Z r1.len) = true by simp at Hrl; simp; word]
  wp_auto
  rw [ite_eq_left (by simp at Hrl; word)]
  wp_apply (wp_load_slice_index r1 (sint.Z (W64 0)) _ dq c (by decide)) $$ [Hr] as Hr
  · iframe; ipureintro; rfl
  wp_join iprop(∃ (f2v : GoMap) (rc : GoSlice) (okv : Bool),
      "f2" ∷ f2_ptr ↦ f2v ∗ "r2" ∷ r2_ptr ↦ rc ∗ "ok2" ∷ ok2_ptr ↦ okv ∗
      "r1" ∷ r1_ptr ↦ r1 ∗
      (if okv then (∃ ov restc, ⌜pOpt (pMap pInt) (c :: rest1') = some (ov, restc)⌝ ∗
          optMapOwn ownPure f2v ov ∗ restOf b dq bs rc restc)
        else (⌜pOpt (pMap pInt) (c :: rest1') = none⌝ ∗ b ↦*{dq} bs)))
    with [f2 r2 ok2 r1 Hr Hback] as ⟨%f2v, %rc, %okv, f2, r2, ok2, r1, Hres⟩
  · -- the presence byte is 0 or 1
    rw [ite_eq_left (by simp at Hrl; word)]
    wp_auto
    rw [ite_eq_left (by simp at Hrl; word)]
    wp_apply (wp_load_slice_index r1 (sint.Z (W64 0)) _ dq c (by decide)) $$ [Hr] as Hr
    · iframe; ipureintro; rfl
    ihave Hrest := restOf_drop' r1 dq (c :: rest1') (W64 1) rest1' (by simp <;> word) rfl $$ Hr
    wp_if_destruct
    · -- 1: a map follows
      icases restOf_open $$ Hrest with ⟨Hr2, Hback2⟩
      wp_apply wp_rpcDec_map_swift_CommandId_int $$ Hr2 as %mpX %rX %okX Hpost
      unfold decPost
      icases Hpost with (⟨%HX, Hr2⟩ | ⟨%lX, %restX, %HX, Hown, HrestX⟩)
      · obtain ⟨HX, rfl⟩ := HX
        wp_join_done
        iexists _, _, false
        rw [ite_eq_right (by simp)]
        iframe
        ihave Hr := Hback2 $$ Hr2
        ihave Hb := Hback $$ Hr
        iframe Hb
        ipureintro; simp [pOpt, HX]
      · obtain ⟨HX, rfl⟩ := HX
        ihave HrestX := restOf_comp $$ Hback2 HrestX
        ihave HrestX := restOf_comp $$ Hback HrestX
        wp_join_done
        iexists _, _, true
        rw [ite_eq_left rfl]
        iframe
        iexists (some lX)
        isplitr
        · ipureintro; simp [pOpt, HX]; word
        simp only [optMapOwn]; iexact Hown
    · -- 0: nil
      have hc : c = W8 0 := by
        have : uint.Z c = 0 ∨ uint.Z c = 1 := by word
        rcases this with h | h
        · word
        · exfalso; apply Hif; word
      subst hc
      ihave Hrest := restOf_comp $$ Hback Hrest
      wp_join_done
      iexists _, _, true
      rw [ite_eq_left rfl]
      iframe
      iexists none
      isplitr
      · ipureintro; simp [pOpt]; word
      unfold optMapOwn; ipureintro; rfl
  · -- the presence byte is above 1
    ihave Hb := Hback $$ Hr
    iexists _, _, false
    rw [ite_eq_right (by simp)]
    iframe
    ipureintro; simp only [pOpt]; rw [ite_eq_right_iff]; intro h; exfalso; word
  cases okv
  · rw [ite_eq_right (by simp)]
    icases Hres with ⟨%Hn, Hb⟩
    wp_auto
    iapply HΦ; ileft; iframe Hb; ipureintro
    refine ⟨?_, rfl⟩
    simp only [pMSync, H, H1, Hn]
  rw [ite_eq_left rfl]
  icases Hres with ⟨%ph, %rest2, %Hph, Hpho, Hrc⟩
  icases restOf_open $$ Hrc with ⟨Hr, Hback⟩
  ihave %Hrl2 := ownSlice_len _ _ _ $$ Hr
  ihave %Hrwf2 := ownSlice_wf _ _ _ $$ Hr
  wp_auto
  rcases hR : rest2 with _ | ⟨c2, rest2'⟩
  · subst hR
    rw [show decide (sint.Z (W64 0) < sint.Z rc.len) = false by simp at Hrl2; simp; word]
    wp_auto
    ihave Hb := Hback $$ Hr
    iapply HΦ; ileft; iframe Hb; ipureintro
    refine ⟨?_, rfl⟩
    simp only [pMSync, H, H1, Hph]; simp [pOpt]
  subst hR
  rw [show decide (sint.Z (W64 0) < sint.Z rc.len) = true by simp at Hrl2; simp; word]
  wp_auto
  rw [ite_eq_left (by simp at Hrl2; word)]
  wp_apply (wp_load_slice_index rc (sint.Z (W64 0)) _ dq c2 (by decide)) $$ [Hr] as Hr
  · iframe; ipureintro; rfl
  wp_join iprop(∃ (f3v : GoMap) (rc2 : GoSlice) (okv2 : Bool),
      "f3" ∷ f3_ptr ↦ f3v ∗ "r3" ∷ r3_ptr ↦ rc2 ∗ "ok3" ∷ ok3_ptr ↦ okv2 ∗
      "r2" ∷ r2_ptr ↦ rc ∗
      (if okv2 then (∃ ov restc, ⌜pOpt (pMap pCmd) (c2 :: rest2') = some (ov, restc)⌝ ∗
          optMapOwn ownCmd f3v ov ∗ restOf b dq bs rc2 restc)
        else (⌜pOpt (pMap pCmd) (c2 :: rest2') = none⌝ ∗ b ↦*{dq} bs)))
    with [f3 r3 ok3 r2 Hr Hback] as ⟨%f3v, %rc2, %okv2, f3, r3, ok3, r2, Hres⟩
  · -- the presence byte is 0 or 1
    rw [ite_eq_left (by simp at Hrl2; word)]
    wp_auto
    rw [ite_eq_left (by simp at Hrl2; word)]
    wp_apply (wp_load_slice_index rc (sint.Z (W64 0)) _ dq c2 (by decide)) $$ [Hr] as Hr
    · iframe; ipureintro; rfl
    ihave Hrest := restOf_drop' rc dq (c2 :: rest2') (W64 1) rest2' (by simp <;> word) rfl $$ Hr
    wp_if_destruct
    · -- 1: a map follows
      icases restOf_open $$ Hrest with ⟨Hr2, Hback2⟩
      wp_apply wp_rpcDec_map_swift_CommandId_state_Command $$ Hr2 as %mpX %rX %okX Hpost
      unfold decPost
      icases Hpost with (⟨%HX, Hr2⟩ | ⟨%lX, %restX, %HX, Hown, HrestX⟩)
      · obtain ⟨HX, rfl⟩ := HX
        wp_join_done
        iexists _, _, false
        rw [ite_eq_right (by simp)]
        iframe
        ihave Hr := Hback2 $$ Hr2
        ihave Hb := Hback $$ Hr
        iframe Hb
        ipureintro; simp [pOpt, HX]
      · obtain ⟨HX, rfl⟩ := HX
        ihave HrestX := restOf_comp $$ Hback2 HrestX
        ihave HrestX := restOf_comp $$ Hback HrestX
        wp_join_done
        iexists _, _, true
        rw [ite_eq_left rfl]
        iframe
        iexists (some lX)
        isplitr
        · ipureintro; simp [pOpt, HX]; word
        simp only [optMapOwn]; iexact Hown
    · -- 0: nil
      have hc : c2 = W8 0 := by
        have : uint.Z c2 = 0 ∨ uint.Z c2 = 1 := by word
        rcases this with h | h
        · word
        · exfalso; apply Hif; word
      subst hc
      ihave Hrest := restOf_comp $$ Hback Hrest
      wp_join_done
      iexists _, _, true
      rw [ite_eq_left rfl]
      iframe
      iexists none
      isplitr
      · ipureintro; simp [pOpt]; word
      unfold optMapOwn; ipureintro; rfl
  · -- the presence byte is above 1
    ihave Hb := Hback $$ Hr
    iexists _, _, false
    rw [ite_eq_right (by simp)]
    iframe
    ipureintro; simp only [pOpt]; rw [ite_eq_right_iff]; intro h; exfalso; word
  cases okv2
  · rw [ite_eq_right (by simp)]
    icases Hres with ⟨%Hn, Hb⟩
    wp_auto
    iapply HΦ; ileft; iframe Hb; ipureintro
    refine ⟨?_, rfl⟩
    simp only [pMSync, H, H1, Hph, Hn]
  rw [ite_eq_left rfl]
  icases Hres with ⟨%cm, %rest3, %Hcm, Hcmo, Hrc⟩
  icases restOf_open $$ Hrc with ⟨Hr, Hback⟩
  ihave %Hrl3 := ownSlice_len _ _ _ $$ Hr
  ihave %Hrwf3 := ownSlice_wf _ _ _ $$ Hr
  wp_auto
  rcases hR : rest3 with _ | ⟨c3, rest3'⟩
  · subst hR
    rw [show decide (sint.Z (W64 0) < sint.Z rc2.len) = false by simp at Hrl3; simp; word]
    wp_auto
    ihave Hb := Hback $$ Hr
    iapply HΦ; ileft; iframe Hb; ipureintro
    refine ⟨?_, rfl⟩
    simp only [pMSync, H, H1, Hph, Hcm]; simp [pOpt]
  subst hR
  rw [show decide (sint.Z (W64 0) < sint.Z rc2.len) = true by simp at Hrl3; simp; word]
  wp_auto
  rw [ite_eq_left (by simp at Hrl3; word)]
  wp_apply (wp_load_slice_index rc2 (sint.Z (W64 0)) _ dq c3 (by decide)) $$ [Hr] as Hr
  · iframe; ipureintro; rfl
  wp_join iprop(∃ (f4v : GoMap) (rc3 : GoSlice) (okv3 : Bool),
      "f4" ∷ f4_ptr ↦ f4v ∗ "r4" ∷ r4_ptr ↦ rc3 ∗ "ok4" ∷ ok4_ptr ↦ okv3 ∗
      "r3" ∷ r3_ptr ↦ rc2 ∗
      (if okv3 then (∃ ov restc, ⌜pOpt (pMap (pList pCmdId)) (c3 :: rest3') = some (ov, restc)⌝ ∗
          optMapOwn ownSliceOf f4v ov ∗ restOf b dq bs rc3 restc)
        else (⌜pOpt (pMap (pList pCmdId)) (c3 :: rest3') = none⌝ ∗ b ↦*{dq} bs)))
    with [f4 r4 ok4 r3 Hr Hback] as ⟨%f4v, %rc3, %okv3, f4, r4, ok4, r3, Hres⟩
  · -- the presence byte is 0 or 1
    rw [ite_eq_left (by simp at Hrl3; word)]
    wp_auto
    rw [ite_eq_left (by simp at Hrl3; word)]
    wp_apply (wp_load_slice_index rc2 (sint.Z (W64 0)) _ dq c3 (by decide)) $$ [Hr] as Hr
    · iframe; ipureintro; rfl
    ihave Hrest := restOf_drop' rc2 dq (c3 :: rest3') (W64 1) rest3' (by simp <;> word) rfl $$ Hr
    wp_if_destruct
    · -- 1: a map follows
      icases restOf_open $$ Hrest with ⟨Hr2, Hback2⟩
      wp_apply wp_rpcDec_map_swift_CommandId_swift_Dep $$ Hr2 as %mpX %rX %okX Hpost
      unfold decPost
      icases Hpost with (⟨%HX, Hr2⟩ | ⟨%lX, %restX, %HX, Hown, HrestX⟩)
      · obtain ⟨HX, rfl⟩ := HX
        wp_join_done
        iexists _, _, false
        rw [ite_eq_right (by simp)]
        iframe
        ihave Hr := Hback2 $$ Hr2
        ihave Hb := Hback $$ Hr
        iframe Hb
        ipureintro; simp [pOpt, HX]
      · obtain ⟨HX, rfl⟩ := HX
        ihave HrestX := restOf_comp $$ Hback2 HrestX
        ihave HrestX := restOf_comp $$ Hback HrestX
        wp_join_done
        iexists _, _, true
        rw [ite_eq_left rfl]
        iframe
        iexists (some lX)
        isplitr
        · ipureintro; simp [pOpt, HX]; word
        simp only [optMapOwn]; iexact Hown
    · -- 0: nil
      have hc : c3 = W8 0 := by
        have : uint.Z c3 = 0 ∨ uint.Z c3 = 1 := by word
        rcases this with h | h
        · word
        · exfalso; apply Hif; word
      subst hc
      ihave Hrest := restOf_comp $$ Hback Hrest
      wp_join_done
      iexists _, _, true
      rw [ite_eq_left rfl]
      iframe
      iexists none
      isplitr
      · ipureintro; simp [pOpt]; word
      unfold optMapOwn; ipureintro; rfl
  · -- the presence byte is above 1
    ihave Hb := Hback $$ Hr
    iexists _, _, false
    rw [ite_eq_right (by simp)]
    iframe
    ipureintro; simp only [pOpt]; rw [ite_eq_right_iff]; intro h; exfalso; word
  cases okv3
  · rw [ite_eq_right (by simp)]
    icases Hres with ⟨%Hn, Hb⟩
    wp_auto
    iapply HΦ; ileft; iframe Hb; ipureintro
    refine ⟨?_, rfl⟩
    simp only [pMSync, H, H1, Hph, Hcm, Hn]
  rw [ite_eq_left rfl]
  icases Hres with ⟨%dp, %rest4, %Hdp, Hdpo, Hrc⟩
  icases restOf_open $$ Hrc with ⟨Hr, Hback⟩
  ihave %Hrl4 := ownSlice_len _ _ _ $$ Hr
  ihave %Hrwf4 := ownSlice_wf _ _ _ $$ Hr
  wp_auto
  ihave Hrest := restOf_close $$ [Hr Hback]
  · iframe
  iapply HΦ; iright; iexists ⟨rep, bal, ph, cm, dp⟩, rest4
  iframe Hrest
  isplitr
  · ipureintro; refine ⟨?_, rfl⟩
    simp only [pMSync, H, H1, Hph, Hcm, Hdp]
  unfold ownSync
  iframe
  ipureintro; exact ⟨rfl, rfl⟩

end wps

end Perennial.github_com.imdea_software.swiftpaxos.examples.swiftnet

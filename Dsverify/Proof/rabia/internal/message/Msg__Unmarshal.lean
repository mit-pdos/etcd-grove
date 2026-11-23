/-
(Ported from dsverify-lab `examples/rabia/proof/Proof/rabia/internal/message/Msg__Unmarshal.lean`, run `rabia-r1wake-1`.)

`(*Msg).Unmarshal` (message.pb.go 1428-1569): decoding `encMsg m` into a zero `Msg` (prover C1).
-/
module

public import Dsverify.Proof.rabia.internal.message.Internal
public import Dsverify.Proof.rabia.internal.message.MsgWire
public import Dsverify.Proof.rabia.internal.message.VarintTac
public import Dsverify.Proof.rabia.internal.message.ConsensusObj__Unmarshal

@[expose] public section

namespace Perennial.rabia.internal.message
open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode model bufio

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [package_sem : rabia.internal.message.Assumptions]
variable [IsPkgInit (IProp GF) pkg_id.rabia.internal.message]

omit [GooseExts] in
theorem w32_ofNat_toNat (x : w32) : BitVec.ofNat 32 x.toNat = x := by simp

omit package_sem [IsPkgInit (IProp GF) pkg_id.rabia.internal.message] in
theorem msgRep_setType (v : Msg) (m : MsgV) (t : w32) (ht : t = m.ty) :
    msgRep (GF := GF) v (m.upto 0) ⊢
      msgRep { Type' := t, Phase' := v.Phase', Value' := v.Value', Obj' := v.Obj' } (m.upto 1) := by
  simp only [msgRep, MsgV.upto, Nat.reduceLT, ite_true, ite_false]
  iintro ⟨%H, H2⟩
  iframe
  ipureintro
  exact ⟨ht, H.2.1, H.2.2⟩

omit package_sem [IsPkgInit (IProp GF) pkg_id.rabia.internal.message] in
theorem msgRep_setPhase (v : Msg) (m : MsgV) (t : w32) (ht : t = m.phase) :
    msgRep (GF := GF) v (m.upto 1) ⊢
      msgRep { Type' := v.Type', Phase' := t, Value' := v.Value', Obj' := v.Obj' } (m.upto 2) := by
  simp only [msgRep, MsgV.upto, Nat.reduceLT, ite_true, ite_false]
  iintro ⟨%H, H2⟩
  iframe
  ipureintro
  exact ⟨H.1, ht, H.2.2⟩

omit package_sem [IsPkgInit (IProp GF) pkg_id.rabia.internal.message] in
theorem msgRep_setValue (v : Msg) (m : MsgV) (t : w32) (ht : t = m.value) :
    msgRep (GF := GF) v (m.upto 2) ⊢
      msgRep { Type' := v.Type', Phase' := v.Phase', Value' := t, Obj' := v.Obj' } (m.upto 3) := by
  simp only [msgRep, MsgV.upto, Nat.reduceLT, ite_true, ite_false]
  iintro ⟨%H, H2⟩
  iframe
  ipureintro
  exact ⟨H.1, H.2.1, ht⟩

omit [GooseExts] in
theorem subslice_of_drop {A : Type} (a : Nat) (l X Y : List A) (h : l.drop a = X ++ Y) :
    subslice a (a + X.length) l = X := by
  rw [subslice_comm, h, Nat.add_sub_cancel_left, List.take_left]

omit package_sem [IsPkgInit (IProp GF) pkg_id.rabia.internal.message] in
theorem msgRep_setObj (v : Msg) (m : MsgV) (o : ObjV) (hobj : m.obj = some o) (p : Loc)
    (ov : ConsensusObj) :
    msgRep (GF := GF) v (m.upto 3) ∗ p ↦□ ov ∗ objRep ov o ⊢
      msgRep { Type' := v.Type', Phase' := v.Phase', Value' := v.Value', Obj' := p } (m.upto 4) := by
  rw [MsgV.upto_four]
  simp only [msgRep, MsgV.upto, Nat.reduceLT, ite_true, ite_false, hobj]
  iintro ⟨⟨%H, _⟩, Hp, Ho⟩
  isplitr
  · ipureintro; exact H
  iexists ov
  iframe

omit package_sem [IsPkgInit (IProp GF) pkg_id.rabia.internal.message] in
theorem msgRep_upto3_obj (v : Msg) (m : MsgV) :
    msgRep (GF := GF) v (m.upto 3) ⊢ ⌜v.Obj' = null⌝ := by
  simp only [msgRep, MsgV.upto, Nat.reduceLT, ite_true, ite_false]
  iintro ⟨_, %H⟩
  ipureintro; exact H

set_option maxHeartbeats 2000000 in
theorem Msg.Unmarshal.wp_proof_of (Hobj : ConsensusObj.Unmarshal.spec (GF := GF)) :
    Msg.Unmarshal.spec (GF := GF) := by
  intro l sl dq m
  wp_start as ⟨Hl, Hsl⟩
  wp_auto
  ihave %Hlen := ownSlice_len _ _ _ $$ Hsl
  ihave HI : (∃ (s : Nat) (v : Msg) (idx : w64),
      "Hl" ∷ l ↦ v ∗ "#Hrep" ∷ msgRep v (m.upto s) ∗ "iNdEx" ∷ iNdEx_ptr ↦ idx ∗
      "%Hs" ∷ ⌜s ≤ 4 ∧ 0 ≤ sint.Z idx ∧ sint.nat idx ≤ (encMsg m).length ∧
        (encMsg m).drop (sint.nat idx) = ((msgSegs m).drop s).flatten⌝ : IProp GF)
      $$ [Hl iNdEx]
  · iexists 0, _, _
    iframe
    simp only [msgRep, MsgV.upto, Nat.not_lt_zero, ite_false]
    ipureintro
    refine ⟨⟨⟨rfl, rfl, rfl⟩, rfl⟩, by omega, by decide, by word, ?_⟩
    rw [encMsg_flatten]; rfl
  wp_for HI
  obtain ⟨Hs, Hidx0, Hidxle, Hrest⟩ := Hs
  wp_if_destruct
  · -- an iteration: the next nonempty field
    replace Hif : sint.Z idx < sint.Z sl.len := by revert Hif; simp
    have hne : ((msgSegs m).drop s).flatten ≠ [] := by
      rw [← Hrest]; intro h
      rw [List.drop_eq_nil_iff] at h; word
    obtain ⟨j, seg, hj1, hj2, hj3, hj4, hj5, hj6⟩ := next_seg _ _ hne
    rw [msgSegs_length] at hj2
    rw [← m.upto_of_empty s j hj1 (by omega) hj3]
    rw [hj6] at Hrest
    clear hj6 hj3 hj1 hne Hs
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl|rfl|rfl|rfl
    · -- field 1: Type
      simp only [msgSegs, List.getElem?_cons_zero, Option.some.injEq] at hj4
      subst hj4
      obtain ⟨hseg, hN⟩ := encScalar_ne_nil hj5
      rw [hseg] at Hrest
      have Hpre0 := Hidx0
      have Hpre : (encMsg m).drop (sint.nat idx) =
          varint 8 ++ (varint (enumNat m.ty) ++ ((msgSegs m).drop (0 + 1)).flatten) := by
        rw [Hrest, varint_lt 8 (by decide)]; rfl
      have HNlt : 8 < 2 ^ 64 := by decide
      varint_loop wire (fun a => wire_ptr ↦ BitVec.ofNat 64 a) 8
        (varint (enumNat m.ty) ++ ((msgSegs m).drop (0 + 1)).flatten) (encMsg m) as i1
      try rw [show W32 (uint.Z ((8#64) >>> W64 3)) = W32 1 from rfl,
        show ((8#64) &&& W64 7) = W64 0 from rfl]
      try wp_auto
      clear Hpre Hpre0 HNlt Hidx0 Hrest
      have Hpre := Hpost
      have Hpre0 := Hpost0
      have HNlt := enumNat_lt m.ty
      clear Hpost Hpost0
      varint_loop Hl (fun a => l ↦ Msg.mk (BitVec.ofNat 32 a) v.Phase' v.Value' v.Obj') (enumNat m.ty) (((msgSegs m).drop (0 + 1)).flatten) (encMsg m) as i2
      rw [ofNat_enumNat]
      wp_for_post
      iframe
      iexists 1, _, _
      iframe
      isplitr
      · iapply msgRep_setType _ _ _ rfl; iexact Hrep
      ipureintro
      exact ⟨by omega, Hpost0, Hpostle, Hpost⟩
    · -- field 2: Phase
      simp only [msgSegs, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hj4
      subst hj4
      obtain ⟨hseg, hN⟩ := encScalar_ne_nil hj5
      rw [hseg] at Hrest
      have Hpre0 := Hidx0
      have Hpre : (encMsg m).drop (sint.nat idx) =
          varint 16 ++ (varint (m.phase.toNat) ++ ((msgSegs m).drop (1 + 1)).flatten) := by
        rw [Hrest, varint_lt 16 (by decide)]; rfl
      have HNlt : 16 < 2 ^ 64 := by decide
      varint_loop wire (fun a => wire_ptr ↦ BitVec.ofNat 64 a) 16
        (varint (m.phase.toNat) ++ ((msgSegs m).drop (1 + 1)).flatten) (encMsg m) as i3
      try rw [show W32 (uint.Z ((16#64) >>> W64 3)) = W32 2 from rfl,
        show ((16#64) &&& W64 7) = W64 0 from rfl]
      try wp_auto
      clear Hpre Hpre0 HNlt Hidx0 Hrest
      have Hpre := Hpost
      have Hpre0 := Hpost0
      have HNlt : m.phase.toNat < 2 ^ 64 := by have := m.phase.isLt; omega
      clear Hpost Hpost0
      varint_loop Hl (fun a => l ↦ Msg.mk v.Type' (BitVec.ofNat 32 a) v.Value' v.Obj') (m.phase.toNat) (((msgSegs m).drop (1 + 1)).flatten) (encMsg m) as i4
      rw [w32_ofNat_toNat]
      wp_for_post
      iframe
      iexists 2, _, _
      iframe
      isplitr
      · iapply msgRep_setPhase _ _ _ rfl; iexact Hrep
      ipureintro
      exact ⟨by omega, Hpost0, Hpostle, Hpost⟩
    · -- field 3: Value
      simp only [msgSegs, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hj4
      subst hj4
      obtain ⟨hseg, hN⟩ := encScalar_ne_nil hj5
      rw [hseg] at Hrest
      have Hpre0 := Hidx0
      have Hpre : (encMsg m).drop (sint.nat idx) =
          varint 24 ++ (varint (m.value.toNat) ++ ((msgSegs m).drop (2 + 1)).flatten) := by
        rw [Hrest, varint_lt 24 (by decide)]; rfl
      have HNlt : 24 < 2 ^ 64 := by decide
      varint_loop wire (fun a => wire_ptr ↦ BitVec.ofNat 64 a) 24
        (varint (m.value.toNat) ++ ((msgSegs m).drop (2 + 1)).flatten) (encMsg m) as i5
      try rw [show W32 (uint.Z ((24#64) >>> W64 3)) = W32 3 from rfl,
        show ((24#64) &&& W64 7) = W64 0 from rfl]
      try wp_auto
      clear Hpre Hpre0 HNlt Hidx0 Hrest
      have Hpre := Hpost
      have Hpre0 := Hpost0
      have HNlt : m.value.toNat < 2 ^ 64 := by have := m.value.isLt; omega
      clear Hpost Hpost0
      varint_loop Hl (fun a => l ↦ Msg.mk v.Type' v.Phase' (BitVec.ofNat 32 a) v.Obj') (m.value.toNat) (((msgSegs m).drop (2 + 1)).flatten) (encMsg m) as i6
      rw [w32_ofNat_toNat]
      wp_for_post
      iframe
      iexists 3, _, _
      iframe
      isplitr
      · iapply msgRep_setValue _ _ _ rfl; iexact Hrep
      ipureintro
      exact ⟨by omega, Hpost0, Hpostle, Hpost⟩
    · -- field 4: Obj
      simp only [msgSegs, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hj4
      subst hj4
      rcases hobj : m.obj with _ | o
      · simp [hobj] at hj5
      simp only [hobj, encBytes] at Hrest
      have Hpre0 := Hidx0
      have Hpre : (encMsg m).drop (sint.nat idx) =
          varint 34 ++ (varint (encObj o).length ++ encObj o ++ ((msgSegs m).drop (3 + 1)).flatten) := by
        rw [Hrest, varint_lt 34 (by decide)]; simp
      have HNlt : 34 < 2 ^ 64 := by decide
      varint_loop wire (fun a => wire_ptr ↦ BitVec.ofNat 64 a) 34
        (varint (encObj o).length ++ encObj o ++ ((msgSegs m).drop (3 + 1)).flatten) (encMsg m) as i7
      try rw [show W32 (uint.Z ((34#64) >>> W64 3)) = W32 4 from rfl,
        show ((34#64) &&& W64 7) = W64 2 from rfl]
      try wp_auto
      clear Hpre Hpre0 HNlt Hidx0 Hrest
      have Hpre := Hpost
      have Hpre0 := Hpost0
      have HNlt : (encObj o).length < 2 ^ 64 := by
        have := congrArg List.length Hpre
        simp only [List.length_drop, List.length_append] at this; word
      clear Hpost Hpost0
      varint_loop msglen (fun a => msglen_ptr ↦ BitVec.ofNat 64 a) (encObj o).length
        (encObj o ++ ((msgSegs m).drop (3 + 1)).flatten) (encMsg m) as i8
      have HLlt : sint.nat i8 + (encObj o).length ≤ (encMsg m).length := by
        have := congrArg List.length Hpost
        simp only [List.length_drop, List.length_append] at this; omega
      wp_if_destruct
      · exfalso; word
      wp_if_destruct
      · exfalso; word
      wp_if_destruct
      · exfalso; word
      ihave %Hnull := msgRep_upto3_obj $$ Hrep
      wp_if_destruct
      rotate_left
      · exact absurd Hnull Hif
      rename_i objp
      ihave %Hwf := ownSlice_wf _ _ _ $$ Hsl
      have Hhi : sint.nat (i8 + BitVec.ofNat 64 (encObj o).length) = sint.nat i8 + (encObj o).length := by
        word
      rw [if_pos ⟨Hpost0, by word, by word⟩]
      have Hb : 0 ≤ sint.Z i8 ∧ sint.Z i8 ≤ sint.Z (i8 + BitVec.ofNat 64 (encObj o).length) ∧
          sint.Z (i8 + BitVec.ofNat 64 (encObj o).length) ≤ sint.Z sl.len := ⟨Hpost0, by word, by word⟩
      icases (ownSlice_slice _ _ sl dq (encMsg m) Hb).1 $$ Hsl with ⟨Hsl1, Hsl2, Hsl3⟩
      rw [Hhi, subslice_of_drop _ _ _ _ Hpost]
      wp_auto
      wp_apply +noauto Hobj $$ [«$r0» Hsl2] as ⟨%ov, Hov, #Hovrep, Hsl2⟩
      · iframe
      ipersist Hov
      wp_auto
      ihave Hsl := (ownSlice_slice _ _ sl dq (encMsg m) Hb).2 $$ [Hsl1 Hsl2 Hsl3]
      · rw [Hhi, subslice_of_drop _ _ _ _ Hpost]; iframe
      wp_for_post
      iframe
      iexists 4, _, _
      iframe
      isplitr
      · iapply msgRep_setObj _ _ _ hobj _ ov
        isplitl []; iexact Hrep
        isplitl []; iexact Hov
        iexact Hovrep
      ipureintro
      refine ⟨by omega, by word, by word, ?_⟩
      rw [Hhi, ← List.drop_drop, Hpost, List.drop_left]
  · -- the end
    replace Hif : ¬ sint.Z idx < sint.Z sl.len := by revert Hif; simp
    have hnil : ((msgSegs m).drop s).flatten = [] := by
      rw [← Hrest, List.drop_eq_nil_iff]; word
    have hm : m.upto s = m := by
      have := m.upto_of_empty s 4 Hs (Nat.le_refl _)
        (fun i h1 h2 => rest_nil _ _ hnil i h1 (by rw [msgSegs_length]; exact h2))
      rw [m.upto_four] at this; exact this.symm
    rw [hm]
    wp_if_destruct
    · exfalso; word
    wp_end
    iexists v
    iframe
    iexact Hrep

theorem Msg.Unmarshal.wp_proof : Msg.Unmarshal.spec (GF := GF) :=
  Msg.Unmarshal.wp_proof_of ConsensusObj.Unmarshal.wp_proof

end proof
end Perennial.rabia.internal.message

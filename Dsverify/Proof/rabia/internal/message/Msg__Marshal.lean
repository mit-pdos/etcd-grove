/-
(Ported from dsverify-lab `examples/rabia/proof/Proof/rabia/internal/message/Msg__Marshal.lean`, run `rabia-r1wake-1`.)

`(*Msg).Size`, `(*Msg).MarshalToSizedBuffer`, `(*Msg).Marshal` (message.pb.go 648-696, 900-920):
the encoder writes `encMsg m` (prover C1b).
-/
module

public import Dsverify.Proof.rabia.internal.message.ConsensusObj__Marshal

@[expose] public section

namespace Perennial.rabia.model

/-- The object field's segment of `encMsg`. -/
def msgObjSeg (m : MsgV) : List w8 :=
  match m.obj with | none => [] | some o => encBytes 0x22 (encObj o)

theorem encMsg_eq (m : MsgV) : encMsg m =
    encScalar 0x08 (enumNat m.ty) ++ (encScalar 0x10 m.phase.toNat ++
      (encScalar 0x18 m.value.toNat ++ msgObjSeg m)) := by
  rcases m with ⟨t, p, va, ob⟩; cases ob <;> simp [encMsg, msgObjSeg]

theorem encMsg_length (m : MsgV) : (encMsg m).length =
    0 + (encScalar 0x08 (enumNat m.ty)).length + (encScalar 0x10 m.phase.toNat).length +
      (encScalar 0x18 m.value.toNat).length + (msgObjSeg m).length := by
  rw [encMsg_eq]; simp only [List.length_append]; omega

theorem msgObjSeg_none (m : MsgV) (h : m.obj = none) : msgObjSeg m = [] := by
  simp [msgObjSeg, h]

theorem msgObjSeg_some (m : MsgV) (o : ObjV) (h : m.obj = some o) :
    msgObjSeg m = encBytes 0x22 (encObj o) := by
  simp [msgObjSeg, h]

theorem W64_sint_enumNat (t : w32) : (W64 (sint.Z t)).toNat = enumNat t := by
  unfold enumNat
  rw [BitVec.signExtend]

theorem varint_enumNat_length (t : w32) : (varint (enumNat t)).length ≤ 10 :=
  varint_length_le _ _ (by have := enumNat_lt t; omega) (by omega)

end Perennial.rabia.model

namespace Perennial.rabia.internal.message
open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode model bufio

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [package_sem : rabia.internal.message.Assumptions]
variable [IsPkgInit (IProp GF) pkg_id.rabia.internal.message]

set_option maxHeartbeats 2000000 in
/-- `(*Msg).Size()`: the length of the encoding. -/
theorem Msg.Size.wp_bounded (l : Loc) (v : Msg) (m : MsgV) (dq : DFrac)
    (hb : (encMsg m).length < 2 ^ 32) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.rabia.internal.message ∗
        isPkgInit (PROP := IProp GF) pkg_id.math.bits ∗ l ↦{dq} v ∗ msgRep v m }}
      (App (Val (l @!! go.GoType.PointerType Msg.ty @!! go!"Size")) (Val #()))
    {{ RET #(W64 (encMsg m).length); l ↦{dq} v }} := by
  wp_start as ⟨Hl, #Hrep⟩
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hl
  unfold msgRep
  icases Hrep with ⟨%Hp, #Hobj⟩
  obtain ⟨hp1, hp2, hp3⟩ := Hp
  icases typedPointsto_split _ _ _ $$ Hl with Hl
  simp only [TypedPointsto.typedPointstoDef]
  icases Hl with ⟨HType, Phase, Value, Obj, -⟩
  wp_auto
  wp_if_destruct
  · exact absurd rfl Hnn
  have hlt : ∀ x : w32, (varint x.toNat).length ≤ 5 := fun x =>
    varint_length_le _ _ (by have := x.isLt; omega) (by omega)
  have hsc : ∀ (t : w8) (x : w32) (s0 : Nat), s0 < 2 ^ 32 → x ≠ 0 →
      W64 (s0 : Nat) + (W64 1 + W64 ((varint x.toNat).length : Nat)) =
        W64 ((s0 + (encScalar t x.toNat).length : Nat) : Int) := by
    intro t x s0 hs0 hx
    have : x.toNat ≠ 0 := fun h => hx (BitVec.eq_of_toNat_eq (by simpa using h))
    rw [encScalar_length, if_neg this]
    have := hlt x
    word
  have hsc0 : ∀ (t : w8) (s0 : Nat), W64 (s0 : Nat) = W64 ((s0 + (encScalar t (W32 0).toNat).length : Nat) : Int) := by
    intro t s0; simp [encScalar]
  have hW : ∀ x : w32, (W64 (uint.Z x)).toNat = x.toNat := by
    intro x; simp [uint.Z]; have := x.isLt; omega
  rw [show (Perennial.zero_val w64) = W64 (0 : Nat) from rfl]
  have hcl := encMsg_length m
  wp_join iprop("n" ∷ n_ptr ↦ W64 ((0 + (encScalar 0x08 (enumNat m.ty)).length : Nat) : Int) ∗ "m" ∷ m_ptr ↦ l ∗
      "HType" ∷ l.[Msg, go!"Type"] ↦{dq} v.Type') with [n m HType] as ⟨n, m, HType⟩
  · rw [hp1] at Hif; rw [Hif]
    rw [show encScalar 0x08 (enumNat (W32 0)) = [] from rfl]
    iframe
  · wp_apply wp_sovMessage
    · iexact Hpkg2
    rw [hp1] at Hif ⊢
    rw [W64_sint_enumNat]
    have hne : (enumNat m.ty) ≠ 0 := fun h => Hif ((enumNat_eq_zero _).1 h)
    have := varint_enumNat_length m.ty
    rw [show W64 ((0 : Nat) : Int) + (W64 1 + W64 ((varint (enumNat m.ty)).length : Nat)) =
        W64 ((0 + (encScalar 0x08 (enumNat m.ty)).length : Nat) : Int) by
      rw [encScalar_length, if_neg hne]; word]
    wp_join_done
  iNamed n; iNamed m; iNamed HType
  wp_join iprop("n" ∷ n_ptr ↦ W64 ((0 + (encScalar 0x08 (enumNat m.ty)).length + (encScalar 0x10 m.phase.toNat).length : Nat) : Int) ∗ "m" ∷ m_ptr ↦ l ∗
      "Phase" ∷ l.[Msg, go!"Phase"] ↦{dq} v.Phase') with [n m Phase] as ⟨n, m, Phase⟩
  · rw [hp2] at Hif; rw [Hif, ← hsc0 0x10 (0 + (encScalar 0x08 (enumNat m.ty)).length)]
    iframe
  · wp_apply wp_sovMessage
    · iexact Hpkg2
    rw [hp2] at Hif ⊢
    rw [hW, hsc 0x10 m.phase (0 + (encScalar 0x08 (enumNat m.ty)).length) (by omega) Hif]
    wp_join_done
  iNamed n; iNamed m; iNamed Phase
  wp_join iprop("n" ∷ n_ptr ↦ W64 ((0 + (encScalar 0x08 (enumNat m.ty)).length + (encScalar 0x10 m.phase.toNat).length + (encScalar 0x18 m.value.toNat).length : Nat) : Int) ∗ "m" ∷ m_ptr ↦ l ∗
      "Value" ∷ l.[Msg, go!"Value"] ↦{dq} v.Value') with [n m Value] as ⟨n, m, Value⟩
  · rw [hp3] at Hif; rw [Hif, ← hsc0 0x18 (0 + (encScalar 0x08 (enumNat m.ty)).length + (encScalar 0x10 m.phase.toNat).length)]
    iframe
  · wp_apply wp_sovMessage
    · iexact Hpkg2
    rw [hp3] at Hif ⊢
    rw [hW, hsc 0x18 m.value (0 + (encScalar 0x08 (enumNat m.ty)).length + (encScalar 0x10 m.phase.toNat).length) (by omega) Hif]
    wp_join_done
  iNamed n; iNamed m; iNamed Value
  obtain ⟨S, hS⟩ : ∃ S, 0 + (encScalar 0x08 (enumNat m.ty)).length + (encScalar 0x10 m.phase.toNat).length +
      (encScalar 0x18 m.value.toNat).length = S := ⟨_, rfl⟩
  rw [hS] at hcl ⊢
  wp_if_destruct
  · cases hmo : m.obj with
    | none =>
      rw [msgObjSeg_none m hmo, List.length_nil, Nat.add_zero] at hcl
      rw [← hcl]
      ihave H := typedPointsto_combine l v dq Hnn $$ [HType Phase Value Obj]
      · simp only [TypedPointsto.typedPointstoDef]; iframe
      iapply HΦ; iexact H
    | some o =>
      icases Hobj with ⟨%ov, #Hov, -⟩
      ihave %Hc := typedPointsto_not_null _ _ _ $$ Hov
      exact absurd Hif Hc
  · cases hmo : m.obj with
    | none =>
      icases Hobj with %Hn
      exact absurd Hn Hif
    | some o =>
      icases Hobj with ⟨%ov, #Hov, #HoRep⟩
      have hseg := msgObjSeg_some m o hmo
      have hEB := encBytes_length 0x22 (encObj o)
      have hsegl := congrArg List.length hseg
      have hbo : (encObj o).length < 2 ^ 32 := by omega
      wp_apply (ConsensusObj.Size.wp_bounded v.Obj' ov o DFrac.discard hbo) $$ [] as -
      · iframe; isplitl []; · iexact Hov
        iexact HoRep
      wp_apply wp_sovMessage
      · iexact Hpkg2
      have hvl := varint_length_le (encObj o).length 5 (by omega) (by omega)
      rw [show (W64 (((encObj o).length : Nat) : Int)).toNat = (encObj o).length by word]
      rw [show W64 ((S : Nat) : Int) + (W64 1 + W64 (((encObj o).length : Nat) : Int) +
          W64 ((varint (encObj o).length).length : Nat)) = W64 (((encMsg m).length : Nat) : Int) by
        rw [hcl, hsegl, hEB]; word]
      ihave H := typedPointsto_combine l v dq Hnn $$ [HType Phase Value Obj]
      · simp only [TypedPointsto.typedPointstoDef]; iframe
      iapply HΦ; iexact H


set_option maxHeartbeats 4000000 in
/-- `(*Msg).MarshalToSizedBuffer(dAtA)`: the encoding written at the end of `dAtA`. -/
theorem Msg.MarshalToSizedBuffer.wp_bounded (l : Loc) (v : Msg) (m : MsgV) (dq : DFrac)
    (sl : GoSlice) (bs : List w8) (hb : (encMsg m).length < 2 ^ 32)
    (hle : (encMsg m).length ≤ bs.length) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.rabia.internal.message ∗
        isPkgInit (PROP := IProp GF) pkg_id.math.bits ∗ l ↦{dq} v ∗ msgRep v m ∗ sl ↦* bs }}
      (App (Val (l @!! go.GoType.PointerType Msg.ty @!! go!"MarshalToSizedBuffer")) (Val #sl))
    {{ RET (PairV #(W64 (encMsg m).length) #interface.nil);
        l ↦{dq} v ∗ sl ↦* (bs.take (bs.length - (encMsg m).length) ++ encMsg m) }} := by
  wp_start as ⟨Hl, #Hrep, Hsl⟩
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hl
  ihave %Hlen := ownSlice_len _ _ _ $$ Hsl
  unfold msgRep
  icases Hrep with ⟨%Hp, #Hobj⟩
  obtain ⟨hp1, hp2, hp3⟩ := Hp
  icases typedPointsto_split _ _ _ $$ Hl with Hl
  simp only [TypedPointsto.typedPointstoDef]
  icases Hl with ⟨HType, Phase, Value, Obj, -⟩
  have hcl := encMsg_length m
  obtain ⟨S, hS⟩ : ∃ S, 0 + (encScalar 0x08 (enumNat m.ty)).length + (encScalar 0x10 m.phase.toNat).length +
      (encScalar 0x18 m.value.toNat).length = S := ⟨_, rfl⟩
  rw [hS] at hcl
  have hL := Hlen.1
  wp_auto
  wp_join iprop(∃ (iv : w64), "i" ∷ i_ptr ↦ iv ∗
      "Hsl" ∷ sl ↦* (bs.take (sint.nat iv) ++ msgObjSeg m) ∗
      "%Hiv" ∷ ⌜0 ≤ sint.Z iv ∧ sint.nat iv + (msgObjSeg m).length = bs.length⌝ ∗
      "Obj" ∷ l.[Msg, go!"Obj"] ↦{dq} v.Obj' ∗ "m" ∷ m_ptr ↦ l ∗
      "dAtA" ∷ dAtA_ptr ↦ sl) with [i Hsl Obj m dAtA] as ⟨%iv, i, Hsl, %Hiv, Obj, m, dAtA⟩
  · cases hmo : m.obj with
    | none =>
      iexists sl.len
      rw [msgObjSeg_none m hmo, List.append_nil, ← hL, List.take_length]
      iframe
      ipureintro; exact ⟨Hlen.2, by simp⟩
    | some o =>
      icases Hobj with ⟨%ov, #Hov, -⟩
      ihave %Hc := typedPointsto_not_null _ _ _ $$ Hov
      exact absurd Hif Hc
  · cases hmo : m.obj with
    | none =>
      icases Hobj with %Hn
      exact absurd Hn Hif
    | some o =>
      icases Hobj with ⟨%ov, #Hov, #HoRep⟩
      have hseg := msgObjSeg_some m o hmo
      have hsegl := congrArg List.length hseg
      have hEB := encBytes_length 0x22 (encObj o)
      have hbo : (encObj o).length < 2 ^ 32 := by omega
      have hEn : (encObj o).length + 1 + (varint (encObj o).length).length ≤ bs.length := by omega
      have hvl := varint_length_le (encObj o).length 5 (by omega) (by omega)
      ihave %Hwf := ownSlice_wf _ _ _ $$ Hsl
      rw [if_pos ⟨by word, by word, by word⟩, ← slice_slice_trivial]
      wp_auto
      wp_apply (ConsensusObj.MarshalToSizedBuffer.wp_bounded v.Obj' ov o DFrac.discard sl bs hbo
        (by omega)) $$ [Hsl] as ⟨-, Hsl⟩
      · iframe; isplitl []; · iexact Hov
        iexact HoRep
      have hiv0 : sint.nat (sl.len - W64 (((encObj o).length : Nat) : Int)) =
          bs.length - (encObj o).length := by word
      have hWc : (W64 (((encObj o).length : Nat) : Int)).toNat = (encObj o).length := by word
      wp_apply (wp_encodeVarintMessage sl (bs.take (bs.length - (encObj o).length) ++ encObj o)
        (sl.len - W64 (((encObj o).length : Nat) : Int)) (W64 (((encObj o).length : Nat) : Int))
        (by word) (by rw [hWc, hiv0]; omega)
        (by rw [hiv0]; simp only [List.length_append, List.length_take]; omega)) $$ [Hsl] as Hsl
      · iexact Hsl
      rw [hWc, hiv0, prepend_writeAt _ _ _ _ (by omega) (by omega)]
      rw [if_pos ⟨by word, by word⟩]
      wp_apply wp_store_slice_index $$ [Hsl] as Hsl
      · iframe; ipureintro; simp only [List.length_append, List.length_take]; word
      rw [show (sint.Z (sl.len - W64 (((encObj o).length : Nat) : Int) -
            W64 ((varint (encObj o).length).length : Nat) - W64 1)).toNat =
          bs.length - (encObj o).length - (varint (encObj o).length).length - 1 by word,
        prepend_set _ _ _ _ (by omega) (by omega)]
      wp_join_done
      iexists _
      rw [hseg]
      unfold encBytes
      rw [show (W8 34 : w8) = (0x22 : w8) from rfl]
      simp only [List.cons_append, List.append_assoc]
      rw [show sint.nat (sl.len - W64 (((encObj o).length : Nat) : Int) -
            W64 ((varint (encObj o).length).length : Nat) - W64 1) =
          bs.length - (encObj o).length - (varint (encObj o).length).length - 1 by word]
      iframe
      ipureintro
      refine ⟨by word, ?_⟩
      simp only [List.length_cons, List.length_append]
      omega
  iNamed i; iNamed Hsl; iNamed Obj; iNamed m; iNamed dAtA
  wp_join iprop(∃ (iv : w64), "i" ∷ i_ptr ↦ iv ∗
      "Hsl" ∷ sl ↦* (bs.take (sint.nat iv) ++ (encScalar 0x18 m.value.toNat ++ msgObjSeg m)) ∗
      "%Hiv" ∷ ⌜0 ≤ sint.Z iv ∧ sint.nat iv + (encScalar 0x18 m.value.toNat ++ msgObjSeg m).length = bs.length⌝ ∗
      "Value" ∷ l.[Msg, go!"Value"] ↦{dq} v.Value' ∗ "m" ∷ m_ptr ↦ l ∗
      "dAtA" ∷ dAtA_ptr ↦ sl) with [i Hsl Value m dAtA] as ⟨%iv, i, Hsl, %Hiv, Value, m, dAtA⟩
  · -- zero: nothing written
    rw [hp3] at Hif
    have hx : m.value.toNat = 0 := by rw [Hif]; rfl
    iexists iv
    rw [show encScalar 0x18 m.value.toNat = [] by rw [encScalar_eq_nil]; exact hx, List.nil_append]
    iframe
    ipureintro; exact Hiv
  · -- nonzero: varint and tag
    rw [hp3] at Hif ⊢
    have hx : m.value.toNat ≠ 0 := fun h => Hif (BitVec.eq_of_toNat_eq (by simpa using h))
    have hsc := encScalar_ne_nil (t := 0x18) (n := m.value.toNat) (by rw [Ne, encScalar_eq_nil]; exact hx)
    have hEn := hle
    rw [hcl, ← hS] at hEn
    have hvl := varint_length_le m.value.toNat 5 (by have := m.value.isLt; omega) (by omega)
    have hW' : (W64 (uint.Z m.value)).toNat = m.value.toNat := by simp [uint.Z]; have := m.value.isLt; omega
    have hlx := encScalar_length 0x18 m.value.toNat
    rw [if_neg hx] at hlx
    have hge : 1 + (varint m.value.toNat).length ≤ sint.nat iv := by
      have := Hiv.2
      try simp only [List.length_append] at this
      omega
    wp_apply (wp_encodeVarintMessage sl (bs.take (sint.nat iv) ++ (msgObjSeg m)) iv (W64 (uint.Z m.value))
      Hiv.1 (by rw [hW']; omega) (by simp only [List.length_append, List.length_take]; omega))
      $$ [Hsl] as Hsl
    · iexact Hsl
    rw [hW', prepend_writeAt _ _ _ _ (by omega) (by omega)]
    rw [if_pos ⟨by word, by word⟩]
    wp_apply wp_store_slice_index $$ [Hsl] as Hsl
    · iframe; ipureintro; simp only [List.length_append, List.length_take]; word
    rw [show (sint.Z (iv - W64 ((varint m.value.toNat).length : Nat) - W64 1)).toNat
        = sint.nat iv - (varint m.value.toNat).length - 1 by word,
      prepend_set _ _ _ _ (by omega) (by omega)]
    wp_join_done
    iexists _
    rw [hsc.1]
    rw [show (W8 24 : w8) = (0x18 : w8) from rfl]
    simp only [List.cons_append]
    rw [show sint.nat (iv - W64 ((varint m.value.toNat).length : Nat) - W64 1) =
      sint.nat iv - (varint m.value.toNat).length - 1 by word]
    iframe
    ipureintro
    refine ⟨by word, ?_⟩
    have := Hiv.2
    simp only [List.length_append, List.length_cons] at this ⊢
    omega
  iNamed i; iNamed Hsl; iNamed Value; iNamed m; iNamed dAtA
  wp_join iprop(∃ (iv : w64), "i" ∷ i_ptr ↦ iv ∗
      "Hsl" ∷ sl ↦* (bs.take (sint.nat iv) ++ (encScalar 0x10 m.phase.toNat ++ (encScalar 0x18 m.value.toNat ++ msgObjSeg m))) ∗
      "%Hiv" ∷ ⌜0 ≤ sint.Z iv ∧ sint.nat iv + (encScalar 0x10 m.phase.toNat ++ (encScalar 0x18 m.value.toNat ++ msgObjSeg m)).length = bs.length⌝ ∗
      "Phase" ∷ l.[Msg, go!"Phase"] ↦{dq} v.Phase' ∗ "m" ∷ m_ptr ↦ l ∗
      "dAtA" ∷ dAtA_ptr ↦ sl) with [i Hsl Phase m dAtA] as ⟨%iv, i, Hsl, %Hiv, Phase, m, dAtA⟩
  · -- zero: nothing written
    rw [hp2] at Hif
    have hx : m.phase.toNat = 0 := by rw [Hif]; rfl
    iexists iv
    rw [show encScalar 0x10 m.phase.toNat = [] by rw [encScalar_eq_nil]; exact hx, List.nil_append]
    iframe
    ipureintro; exact Hiv
  · -- nonzero: varint and tag
    rw [hp2] at Hif ⊢
    have hx : m.phase.toNat ≠ 0 := fun h => Hif (BitVec.eq_of_toNat_eq (by simpa using h))
    have hsc := encScalar_ne_nil (t := 0x10) (n := m.phase.toNat) (by rw [Ne, encScalar_eq_nil]; exact hx)
    have hEn := hle
    rw [hcl, ← hS] at hEn
    have hvl := varint_length_le m.phase.toNat 5 (by have := m.phase.isLt; omega) (by omega)
    have hW' : (W64 (uint.Z m.phase)).toNat = m.phase.toNat := by simp [uint.Z]; have := m.phase.isLt; omega
    have hlx := encScalar_length 0x10 m.phase.toNat
    rw [if_neg hx] at hlx
    have hge : 1 + (varint m.phase.toNat).length ≤ sint.nat iv := by
      have := Hiv.2
      try simp only [List.length_append] at this
      omega
    wp_apply (wp_encodeVarintMessage sl (bs.take (sint.nat iv) ++ (encScalar 0x18 m.value.toNat ++ msgObjSeg m)) iv (W64 (uint.Z m.phase))
      Hiv.1 (by rw [hW']; omega) (by simp only [List.length_append, List.length_take]; omega))
      $$ [Hsl] as Hsl
    · iexact Hsl
    rw [hW', prepend_writeAt _ _ _ _ (by omega) (by omega)]
    rw [if_pos ⟨by word, by word⟩]
    wp_apply wp_store_slice_index $$ [Hsl] as Hsl
    · iframe; ipureintro; simp only [List.length_append, List.length_take]; word
    rw [show (sint.Z (iv - W64 ((varint m.phase.toNat).length : Nat) - W64 1)).toNat
        = sint.nat iv - (varint m.phase.toNat).length - 1 by word,
      prepend_set _ _ _ _ (by omega) (by omega)]
    wp_join_done
    iexists _
    rw [hsc.1]
    rw [show (W8 16 : w8) = (0x10 : w8) from rfl]
    simp only [List.cons_append]
    rw [show sint.nat (iv - W64 ((varint m.phase.toNat).length : Nat) - W64 1) =
      sint.nat iv - (varint m.phase.toNat).length - 1 by word]
    iframe
    ipureintro
    refine ⟨by word, ?_⟩
    have := Hiv.2
    simp only [List.length_append, List.length_cons] at this ⊢
    omega
  iNamed i; iNamed Hsl; iNamed Phase; iNamed m; iNamed dAtA
  wp_join iprop(∃ (iv : w64), "i" ∷ i_ptr ↦ iv ∗
      "Hsl" ∷ sl ↦* (bs.take (sint.nat iv) ++ (encScalar 0x08 (enumNat m.ty) ++ (encScalar 0x10 m.phase.toNat ++ (encScalar 0x18 m.value.toNat ++ msgObjSeg m)))) ∗
      "%Hiv" ∷ ⌜0 ≤ sint.Z iv ∧ sint.nat iv + (encScalar 0x08 (enumNat m.ty) ++ (encScalar 0x10 m.phase.toNat ++ (encScalar 0x18 m.value.toNat ++ msgObjSeg m))).length = bs.length⌝ ∗
      "HType" ∷ l.[Msg, go!"Type"] ↦{dq} v.Type' ∗ "m" ∷ m_ptr ↦ l ∗
      "dAtA" ∷ dAtA_ptr ↦ sl) with [i Hsl HType m dAtA] as ⟨%iv, i, Hsl, %Hiv, HType, m, dAtA⟩
  · -- zero: nothing written
    rw [hp1] at Hif
    have hx : (enumNat m.ty) = 0 := by rw [Hif]; rfl
    iexists iv
    rw [show encScalar 0x08 (enumNat m.ty) = [] by rw [encScalar_eq_nil]; exact hx, List.nil_append]
    iframe
    ipureintro; exact Hiv
  · -- nonzero: varint and tag
    rw [hp1] at Hif ⊢
    have hx : (enumNat m.ty) ≠ 0 := fun h => Hif ((enumNat_eq_zero _).1 h)
    have hsc := encScalar_ne_nil (t := 0x08) (n := (enumNat m.ty)) (by rw [Ne, encScalar_eq_nil]; exact hx)
    have hEn := hle
    rw [hcl, ← hS] at hEn
    have hvl := varint_enumNat_length m.ty
    have hW' : (W64 (sint.Z m.ty)).toNat = enumNat m.ty := W64_sint_enumNat m.ty
    have hlx := encScalar_length 0x08 (enumNat m.ty)
    rw [if_neg hx] at hlx
    have hge : 1 + (varint (enumNat m.ty)).length ≤ sint.nat iv := by
      have := Hiv.2
      try simp only [List.length_append] at this
      omega
    wp_apply (wp_encodeVarintMessage sl (bs.take (sint.nat iv) ++ (encScalar 0x10 m.phase.toNat ++ (encScalar 0x18 m.value.toNat ++ msgObjSeg m))) iv (W64 (sint.Z m.ty))
      Hiv.1 (by rw [hW']; omega) (by simp only [List.length_append, List.length_take]; omega))
      $$ [Hsl] as Hsl
    · iexact Hsl
    rw [hW', prepend_writeAt _ _ _ _ (by omega) (by omega)]
    rw [if_pos ⟨by word, by word⟩]
    wp_apply wp_store_slice_index $$ [Hsl] as Hsl
    · iframe; ipureintro; simp only [List.length_append, List.length_take]; word
    rw [show (sint.Z (iv - W64 ((varint (enumNat m.ty)).length : Nat) - W64 1)).toNat
        = sint.nat iv - (varint (enumNat m.ty)).length - 1 by word,
      prepend_set _ _ _ _ (by omega) (by omega)]
    wp_join_done
    iexists _
    rw [hsc.1]
    rw [show (W8 8 : w8) = (0x08 : w8) from rfl]
    simp only [List.cons_append]
    rw [show sint.nat (iv - W64 ((varint (enumNat m.ty)).length : Nat) - W64 1) =
      sint.nat iv - (varint (enumNat m.ty)).length - 1 by word]
    iframe
    ipureintro
    refine ⟨by word, ?_⟩
    have := Hiv.2
    simp only [List.length_append, List.length_cons] at this ⊢
    omega
  iNamed i; iNamed Hsl; iNamed HType; iNamed m; iNamed dAtA
  rw [← encMsg_eq] at Hiv ⊢
  ihave H := typedPointsto_combine l v dq Hnn $$ [HType Phase Value Obj]
  · simp only [TypedPointsto.typedPointstoDef]; iframe
  rw [show sl.len - iv = W64 ((encMsg m).length : Nat) by word,
    show bs.length - (encMsg m).length = sint.nat iv by omega]
  iapply HΦ
  iframe

set_option maxHeartbeats 1000000 in
/-- `(*Msg).Marshal()`, generic in the package instance; the `isPkgInit` of `math/bits`
taken as a premise. -/
theorem Msg.Marshal.wp_gen (l : Loc) (v : Msg) (m : MsgV) (dq : DFrac)
    (hb : (encMsg m).length < 2 ^ 32) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.rabia.internal.message ∗
        isPkgInit (PROP := IProp GF) pkg_id.math.bits ∗ l ↦{dq} v ∗ msgRep v m }}
      (App (Val (l @!! go.GoType.PointerType Msg.ty @!! go!"Marshal")) (Val #()))
    {{ (sl : GoSlice), RET (PairV #sl #interface.nil); l ↦{dq} v ∗ sl ↦* encMsg m }} := by
  wp_start as ⟨Hl, #Hrep⟩
  wp_auto
  wp_apply (Msg.Size.wp_bounded l v m dq hb) $$ [Hl] as Hl
  · iframe; iexact Hrep
  wp_apply (wp_slice_make2 (V := w8) (W64 ((encMsg m).length : Nat))) as %sl ⟨Hsl, -⟩
  · ipureintro; word
  ihave %Hsll := ownSlice_len _ _ _ $$ Hsl
  ihave %Hslw := ownSlice_wf _ _ _ $$ Hsl
  have hsllen : sl.len = W64 ((encMsg m).length : Nat) := by
    simp only [List.length_replicate] at Hsll; word
  rw [if_pos ⟨by word, by word, by word⟩, ← hsllen, ← slice_slice_trivial]
  wp_auto
  wp_apply (Msg.MarshalToSizedBuffer.wp_bounded l v m dq sl
    (List.replicate (sint.nat sl.len) (Perennial.zero_val w8)) hb
    (by rw [List.length_replicate, hsllen]; word)) $$ [Hl Hsl]
    as ⟨Hl, Hsl⟩
  · iframe; iexact Hrep
  simp only [List.length_replicate, show sint.nat sl.len = (encMsg m).length
    by rw [hsllen]; word, Nat.sub_self, List.take_zero, List.nil_append]
  rw [if_pos ⟨by word, by word, by word⟩, ← hsllen, ← slice_slice_trivial]
  wp_auto
  wp_end

end proof
end Perennial.rabia.internal.message

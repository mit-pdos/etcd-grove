/-
(Ported from dsverify-lab `examples/rabia/proof/Proof/rabia/internal/message/Command__Marshal.lean`, run `rabia-r1wake-1`.)

`(*Command).Size`, `(*Command).MarshalToSizedBuffer`, `(*Command).Marshal`
(message.pb.go 508-553, 835-857): the encoder writes `encCmd c` (prover C1).
-/
module

public import Dsverify.Proof.rabia.internal.message.Internal
public import Dsverify.Proof.rabia.internal.message.Encode
public import Dsverify.Proof.rabia.internal.message.MsgWire

@[expose] public section

namespace Perennial.rabia.model

theorem encScalar_length (t : w8) (n : Nat) :
    (encScalar t n).length = if n = 0 then 0 else 1 + (varint n).length := by
  unfold encScalar; split <;> simp; omega

theorem encBytes_length (t : w8) (bs : List w8) :
    (encBytes t bs).length = 1 + (varint bs.length).length + bs.length := by
  simp [encBytes]; omega

theorem flatMap_take_succ {α β} (f : α → List β) (l : List α) (i : Nat) (h : i < l.length) :
    ((l.take (i + 1)).flatMap f).length = ((l.take i).flatMap f).length + (f l[i]).length := by
  rw [List.take_add_one, List.getElem?_eq_getElem h]
  simp only [Option.toList_some, List.flatMap_append, List.length_append, List.flatMap_cons,
    List.flatMap_nil, List.append_nil]

theorem prepend_writeAt (bs E X : List w8) (i : Nat) (hX : X.length ≤ i) (hi : i ≤ bs.length) :
    writeAt (bs.take i ++ E) (i - X.length) X = bs.take (i - X.length) ++ (X ++ E) := by
  unfold writeAt
  have h1 : (bs.take i ++ E).take (i - X.length) = bs.take (i - X.length) := by
    rw [List.take_append_of_le_length (by simp; omega), List.take_take, Nat.min_eq_left (by omega)]
  have h2 : (bs.take i ++ E).drop (i - X.length + X.length) = E := by
    rw [show i - X.length + X.length = i by omega, List.drop_append_of_le_length (by simp; omega)]
    simp
  rw [h1, h2, List.append_assoc]

theorem prepend_set (bs E : List w8) (i : Nat) (t : w8) (h1 : 1 ≤ i) (hi : i ≤ bs.length) :
    (bs.take i ++ E).set (i - 1) t = bs.take (i - 1) ++ (t :: E) := by
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  have : bs.take (j + 1) = bs.take j ++ [bs[j]] := by
    rw [List.take_add_one, List.getElem?_eq_getElem (by omega)]
    simp
  rw [this, List.append_assoc, show j + 1 - 1 = j by omega,
    List.set_append_right _ _ (by simp; omega)]
  have : j - (bs.take j).length = 0 := by simp; omega
  rw [this]; rfl

theorem take_prefix (bs E : List w8) (iv iv1 : Nat) (h1 : iv1 ≤ iv) (h2 : iv ≤ bs.length) :
    (bs.take iv ++ E).take iv1 = bs.take iv1 := by
  rw [List.take_append_of_le_length (by simp; omega), List.take_take, Nat.min_eq_left h1]

theorem subslice_prefix (bs E : List w8) (iv iv1 L : Nat) (h1 : iv1 ≤ iv) (h2 : iv ≤ bs.length)
    (hL : iv + E.length = L) :
    subslice iv1 L (bs.take iv ++ E) = (bs.take iv).drop iv1 ++ E := by
  rw [subslice_comm, List.drop_append_of_le_length (by simp; omega)]
  rw [List.take_of_length_le (by simp; omega)]

theorem drop_prefix (bs E : List w8) (iv L : Nat) (h2 : iv ≤ bs.length) (hL : iv + E.length = L) :
    (bs.take iv ++ E).drop L = [] := by
  rw [List.drop_eq_nil_iff]; simp; omega

theorem flatMap_take_le {α β} (f : α → List β) (l : List α) (i : Nat) :
    ((l.take i).flatMap f).length ≤ (l.flatMap f).length := by
  conv => rhs; rw [← List.take_append_drop i l]
  simp only [List.flatMap_append, List.length_append]; omega

theorem encCmd_length (c : CmdV) : (encCmd c).length =
    0 + (encScalar 0x08 c.cliId.toNat).length + (encScalar 0x10 c.cliSeq.toNat).length +
      (encScalar 0x18 c.svrSeq.toNat).length + (c.commands.flatMap (encBytes 0x22)).length := by
  simp only [encCmd, List.length_append]; omega

end Perennial.rabia.model

namespace Perennial.rabia.internal.message
open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode model bufio

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [package_sem : rabia.internal.message.Assumptions]
variable [IsPkgInit (IProp GF) pkg_id.rabia.internal.message]

set_option maxHeartbeats 1000000 in
/-- `(*Command).Size()`: the length of the encoding. -/
theorem Command.Size.wp_bounded (l : Loc) (v : Command) (c : CmdV) (dq : DFrac)
    (hb : (encCmd c).length < 2 ^ 33) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.rabia.internal.message ∗
        isPkgInit (PROP := IProp GF) pkg_id.math.bits ∗ l ↦{dq} v ∗ cmdRep v c }}
      (App (Val (l @!! go.GoType.PointerType Command.ty @!! go!"Size")) (Val #()))
    {{ RET #(W64 (encCmd c).length); l ↦{dq} v }} := by
  wp_start as ⟨Hl, #Hrep⟩
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hl
  unfold cmdRep
  icases Hrep with ⟨%Hp, #Hcmds⟩
  obtain ⟨hp1, hp2, hp3⟩ := Hp
  icases typedPointsto_split _ _ _ $$ Hl with Hl
  simp only [TypedPointsto.typedPointstoDef]
  icases Hl with ⟨CliId, CliSeq, SvrSeq, Commands, -⟩
  wp_auto
  wp_if_destruct
  · exact absurd rfl Hnn
  have hlt : ∀ x : w32, (varint x.toNat).length ≤ 5 := fun x =>
    varint_length_le _ _ (by have := x.isLt; omega) (by omega)
  have hsc : ∀ (t : w8) (x : w32) (s0 : Nat), s0 < 2 ^ 33 → x ≠ 0 →
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
  have hcl := encCmd_length c
  wp_join iprop("n" ∷ n_ptr ↦ W64 ((0 + (encScalar 0x08 c.cliId.toNat).length : Nat) : Int) ∗ "m" ∷ m_ptr ↦ l ∗
      "CliId" ∷ l.[Command, go!"CliId"] ↦{dq} v.CliId') with [n m CliId] as ⟨n, m, CliId⟩
  · rw [hp1] at Hif; rw [Hif, ← hsc0 0x08 (0)]
    iframe
  · wp_apply wp_sovMessage
    · iexact Hpkg2
    rw [hp1] at Hif ⊢
    rw [hW, hsc 0x08 c.cliId (0) (by omega) Hif]
    wp_join_done
  iNamed n; iNamed m; iNamed CliId
  wp_join iprop("n" ∷ n_ptr ↦ W64 ((0 + (encScalar 0x08 c.cliId.toNat).length + (encScalar 0x10 c.cliSeq.toNat).length : Nat) : Int) ∗ "m" ∷ m_ptr ↦ l ∗
      "CliSeq" ∷ l.[Command, go!"CliSeq"] ↦{dq} v.CliSeq') with [n m CliSeq] as ⟨n, m, CliSeq⟩
  · rw [hp2] at Hif; rw [Hif, ← hsc0 0x10 (0 + (encScalar 0x08 c.cliId.toNat).length)]
    iframe
  · wp_apply wp_sovMessage
    · iexact Hpkg2
    rw [hp2] at Hif ⊢
    rw [hW, hsc 0x10 c.cliSeq (0 + (encScalar 0x08 c.cliId.toNat).length) (by omega) Hif]
    wp_join_done
  iNamed n; iNamed m; iNamed CliSeq
  wp_join iprop("n" ∷ n_ptr ↦ W64 ((0 + (encScalar 0x08 c.cliId.toNat).length + (encScalar 0x10 c.cliSeq.toNat).length + (encScalar 0x18 c.svrSeq.toNat).length : Nat) : Int) ∗ "m" ∷ m_ptr ↦ l ∗
      "SvrSeq" ∷ l.[Command, go!"SvrSeq"] ↦{dq} v.SvrSeq') with [n m SvrSeq] as ⟨n, m, SvrSeq⟩
  · rw [hp3] at Hif; rw [Hif, ← hsc0 0x18 (0 + (encScalar 0x08 c.cliId.toNat).length + (encScalar 0x10 c.cliSeq.toNat).length)]
    iframe
  · wp_apply wp_sovMessage
    · iexact Hpkg2
    rw [hp3] at Hif ⊢
    rw [hW, hsc 0x18 c.svrSeq (0 + (encScalar 0x08 c.cliId.toNat).length + (encScalar 0x10 c.cliSeq.toNat).length) (by omega) Hif]
    wp_join_done
  iNamed n; iNamed m; iNamed SvrSeq
  generalize hS : 0 + (encScalar 0x08 c.cliId.toNat).length + (encScalar 0x10 c.cliSeq.toNat).length +
      (encScalar 0x18 c.svrSeq.toNat).length = S at hcl
  ihave %Hcl := ownSlice_len _ _ _ $$ Hcmds
  wp_if_destruct
  · -- the commands
    ihave HI : (∃ (i : w64) (sv : GoString) (lv : w64), "i" ∷ i_ptr ↦ i ∗
        "n" ∷ n_ptr ↦ W64 ((S + ((c.commands.take (sint.nat i)).flatMap (encBytes 0x22)).length : Nat) : Int) ∗
        "s" ∷ s_ptr ↦ sv ∗ "l" ∷ l_ptr ↦ lv ∗
        "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.nat i ≤ c.commands.length⌝ : IProp GF) $$ [i n s l]
    · iexists _, _, _
      iframe
      simp only [show sint.nat (W64 0) = 0 from rfl, List.take_zero, List.flatMap_nil,
        List.length_nil, Nat.add_zero]
      iframe
      ipureintro; exact ⟨by decide, by omega⟩
    wp_for HI
    wp_if_destruct
    · obtain ⟨Hi1, Hi2⟩ := Hi
      have hilt : sint.nat i < c.commands.length := by word
      rw [if_pos ⟨Hi1, by word⟩]
      list_elem c.commands (sint.nat i) as cmd
      wp_apply wp_load_slice_index _ (sint.Z i) c.commands DFrac.discard cmd Hi1 $$ [] as -
      · isplitl []; · iexact Hcmds
        ipureintro; rw [show (sint.Z i).toNat = sint.nat i by word]; exact Hcmd_lookup
      wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %Hslen
      wp_apply wp_sovMessage
      · iexact Hpkg2
      have hcmdi : c.commands[sint.nat i] = cmd := by
        rw [List.getElem?_eq_some_iff] at Hcmd_lookup; exact Hcmd_lookup.2
      have hP := flatMap_take_succ (encBytes 0x22) c.commands (sint.nat i) hilt
      rw [hcmdi, encBytes_length] at hP
      have hPle : ((c.commands.take (sint.nat i + 1)).flatMap (encBytes 0x22)).length ≤
          (c.commands.flatMap (encBytes 0x22)).length := by
        have := flatMap_take_le (encBytes 0x22) c.commands (sint.nat i + 1); omega
      have hvl := varint_length_le cmd.length 10 (by omega) (by omega)
      have hW2 : (W64 (cmd.length : Nat)).toNat = cmd.length := by word
      rw [hW2]
      wp_for_post
      iframe
      iexists _, _, _
      iframe
      rw [show sint.nat (i + W64 1) = sint.nat i + 1 by word]
      rw [show W64 ((S + ((c.commands.take (sint.nat i)).flatMap (encBytes 0x22)).length : Nat) : Int) +
          (W64 1 + W64 (cmd.length : Nat) + W64 ((varint cmd.length).length : Nat)) =
          W64 ((S + ((c.commands.take (sint.nat i + 1)).flatMap (encBytes 0x22)).length : Nat) : Int) by
        rw [hP]; word]
      iframe
      ipureintro; exact ⟨by word, by word⟩
    · -- the loop's end
      obtain ⟨Hi1, Hi2⟩ := Hi
      rw [show sint.nat i = c.commands.length by word, List.take_length, ← hcl]
      ihave H := typedPointsto_combine l v dq Hnn $$ [CliId CliSeq SvrSeq Commands]
      · simp only [TypedPointsto.typedPointstoDef]; iframe
      wp_end
  · -- no commands
    have hnil : c.commands = [] := by
      apply List.eq_nil_of_length_eq_zero; word
    rw [hnil, List.flatMap_nil, List.length_nil, Nat.add_zero] at hcl
    rw [← hcl]
    ihave H := typedPointsto_combine l v dq Hnn $$ [CliId CliSeq SvrSeq Commands]
    · simp only [TypedPointsto.typedPointstoDef]; iframe
    wp_end

set_option maxHeartbeats 2000000 in
/-- `(*Command).MarshalToSizedBuffer(dAtA)`: the encoding written at the end of `dAtA`. -/
theorem Command.MarshalToSizedBuffer.wp_bounded (l : Loc) (v : Command) (c : CmdV) (dq : DFrac)
    (sl : GoSlice) (bs : List w8) (hb : (encCmd c).length < 2 ^ 33)
    (hle : (encCmd c).length ≤ bs.length) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.rabia.internal.message ∗
        isPkgInit (PROP := IProp GF) pkg_id.math.bits ∗ l ↦{dq} v ∗ cmdRep v c ∗ sl ↦* bs }}
      (App (Val (l @!! go.GoType.PointerType Command.ty @!! go!"MarshalToSizedBuffer")) (Val #sl))
    {{ RET (PairV #(W64 (encCmd c).length) #interface.nil);
        l ↦{dq} v ∗ sl ↦* (bs.take (bs.length - (encCmd c).length) ++ encCmd c) }} := by
  wp_start as ⟨Hl, #Hrep, Hsl⟩
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hl
  ihave %Hlen := ownSlice_len _ _ _ $$ Hsl
  unfold cmdRep
  icases Hrep with ⟨%Hp, #Hcmds⟩
  obtain ⟨hp1, hp2, hp3⟩ := Hp
  icases typedPointsto_split _ _ _ $$ Hl with Hl
  simp only [TypedPointsto.typedPointstoDef]
  icases Hl with ⟨CliId, CliSeq, SvrSeq, Commands, -⟩
  ihave %Hcl := ownSlice_len _ _ _ $$ Hcmds
  have hcl := encCmd_length c
  generalize hS : 0 + (encScalar 0x08 c.cliId.toNat).length + (encScalar 0x10 c.cliSeq.toNat).length +
      (encScalar 0x18 c.svrSeq.toNat).length = S at hcl
  have hL := Hlen.1
  wp_auto
  wp_join iprop(∃ (iv : w64), "i" ∷ i_ptr ↦ iv ∗
      "Hsl" ∷ sl ↦* (bs.take (sint.nat iv) ++ c.commands.flatMap (encBytes 0x22)) ∗
      "%Hiv" ∷ ⌜0 ≤ sint.Z iv ∧ sint.nat iv + (c.commands.flatMap (encBytes 0x22)).length = bs.length⌝ ∗
      "Commands" ∷ l.[Command, go!"Commands"] ↦{dq} v.Commands' ∗ "m" ∷ m_ptr ↦ l ∗
      "dAtA" ∷ dAtA_ptr ↦ sl) with [i Hsl Commands m dAtA] as ⟨%iv, i, Hsl, %Hiv, Commands, m, dAtA⟩
  · -- the commands, back to front
    ihave HI : (∃ (k : Nat) (it iv : w64), "iNdEx" ∷ iNdEx_ptr ↦ it ∗ "i" ∷ i_ptr ↦ iv ∗
        "Hsl" ∷ sl ↦* (bs.take (sint.nat iv) ++ (c.commands.drop k).flatMap (encBytes 0x22)) ∗
        "%Hk" ∷ ⌜k ≤ c.commands.length ∧ sint.Z it = (k : Int) - 1 ∧ 0 ≤ sint.Z iv ∧
          sint.nat iv + ((c.commands.drop k).flatMap (encBytes 0x22)).length = bs.length⌝ : IProp GF)
        $$ [iNdEx i Hsl]
    · iexists c.commands.length, _, _
      rw [List.drop_length, List.flatMap_nil, List.append_nil, ← hL, List.take_length]
      iframe
      ipureintro; exact ⟨Nat.le_refl _, by word, Hlen.2, by simp⟩
    wp_for HI
    obtain ⟨Hk1, Hk2, Hk3, Hk4⟩ := Hk
    wp_if_destruct
    · -- one command, k - 1
      replace Hif : 0 ≤ sint.Z it := by
        first | exact Hif | (revert Hif; simp)
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by word⟩
      have hk' : k' < c.commands.length := by omega
      list_elem c.commands k' as cmd
      have hcmd : c.commands[k'] = cmd := by
        rw [List.getElem?_eq_some_iff] at Hcmd_lookup; exact Hcmd_lookup.2
      have hE : (c.commands.drop k').flatMap (encBytes 0x22) =
          encBytes 0x22 cmd ++ (c.commands.drop (k' + 1)).flatMap (encBytes 0x22) := by
        rw [List.drop_eq_getElem_cons hk', hcmd]; simp
      generalize hEdef : (c.commands.drop (k' + 1)).flatMap (encBytes 0x22) = E at Hk4 hE ⊢
      have hEl := congrArg List.length hE
      simp only [List.length_append, encBytes_length] at hEl
      have hEle : ((c.commands.drop k').flatMap (encBytes 0x22)).length ≤
          (c.commands.flatMap (encBytes 0x22)).length := by
        conv => rhs; rw [← List.take_append_drop k' c.commands]
        simp only [List.flatMap_append, List.length_append]; omega
      have hvl := varint_length_le cmd.length 10 (by omega) (by omega)
      rw [if_pos ⟨by word, by word⟩]
      wp_apply wp_load_slice_index _ (sint.Z it) c.commands DFrac.discard cmd (by word) $$ [] as -
      · isplitl []; · iexact Hcmds
        ipureintro; rw [show (sint.Z it).toNat = k' by word]; exact Hcmd_lookup
      wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %Hslen
      ihave %Hwf := ownSlice_wf _ _ _ $$ Hsl
      have hEle2 := hle
      rw [hcl] at hEle2
      have hcmdle : cmd.length + 1 + (varint cmd.length).length ≤ sint.nat iv := by omega
      have hiv1 : sint.nat (iv - W64 (cmd.length : Nat)) = sint.nat iv - cmd.length := by word
      have Hb : 0 ≤ sint.Z (iv - W64 (cmd.length : Nat)) ∧
          sint.Z (iv - W64 (cmd.length : Nat)) ≤ sint.Z sl.len ∧ sint.Z sl.len ≤ sint.Z sl.len :=
        ⟨by word, by word, Int.le_refl _⟩
      rw [if_pos ⟨Hb.1, Hb.2.1, by word⟩]
      icases (ownSlice_slice _ _ sl (DFrac.own 1) _ Hb).1 $$ Hsl with ⟨Hs1, Hs2, Hs3⟩
      have hLn : sint.nat sl.len = bs.length := by word
      have hsub := subslice_prefix bs E (sint.nat iv) (sint.nat iv - cmd.length) (sint.nat sl.len)
        (by omega) (by omega) (by omega)
      have hsubl : ((bs.take (sint.nat iv)).drop (sint.nat iv - cmd.length)).length = cmd.length := by
        simp; omega
      rw [hiv1, hsub, take_prefix _ _ _ _ (by omega) (by omega),
        drop_prefix _ _ _ _ (by omega) (by omega)]
      generalize hX : (bs.take (sint.nat iv)).drop (sint.nat iv - cmd.length) = X at hsubl
      wp_auto
      rw [if_pos ⟨by word, by word⟩]
      wp_apply wp_load_slice_index _ (sint.Z it) c.commands DFrac.discard cmd (by word) $$ [] as -
      · isplitl []; · iexact Hcmds
        ipureintro; rw [show (sint.Z it).toNat = k' by word]; exact Hcmd_lookup
      wp_apply wp_string_to_bytes as %cb ⟨Hcb, -⟩
      wp_apply wp_slice_copy $$ [Hs2 Hcb] as %ncp ⟨%Hncp, Hs2, -⟩
      · iframe
      have hce : cmd.take (X ++ E).length ++ (X ++ E).drop cmd.length = cmd ++ E := by
        rw [List.take_of_length_le (by simp; omega), List.drop_append_of_le_length (by omega),
          List.drop_of_length_le (by omega), List.nil_append]
      rw [hce]
      ihave Hsl := (ownSlice_slice _ _ sl (DFrac.own 1)
        (bs.take (sint.nat iv - cmd.length) ++ (cmd ++ E)) Hb).2 $$ [Hs1 Hs2 Hs3]
      · rw [hiv1, take_prefix _ _ _ _ (Nat.le_refl _) (by omega),
          subslice_prefix _ _ _ _ _ (Nat.le_refl _) (by omega) (by simp; omega),
          drop_prefix _ _ _ _ (by omega) (by simp; omega)]
        simp only [List.drop_take, Nat.sub_self, List.take_zero, List.nil_append]
        iframe
      rw [if_pos ⟨by word, by word⟩]
      wp_apply wp_load_slice_index _ (sint.Z it) c.commands DFrac.discard cmd (by word) $$ [] as -
      · isplitl []; · iexact Hcmds
        ipureintro; rw [show (sint.Z it).toNat = k' by word]; exact Hcmd_lookup
      wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %-
      have hWc : (W64 (cmd.length : Nat)).toNat = cmd.length := by word
      wp_apply (wp_encodeVarintMessage sl (bs.take (sint.nat iv - cmd.length) ++ (cmd ++ E))
        (iv - W64 (cmd.length : Nat)) (W64 (cmd.length : Nat))
        (by word) (by rw [hWc, hiv1]; omega)
        (by rw [hiv1]; simp only [List.length_append, List.length_take]; omega)) $$ [Hsl] as Hsl
      · iexact Hsl
      rw [hWc, hiv1, prepend_writeAt _ _ _ _ (by omega) (by omega)]
      have hiv2 : sint.nat (iv - W64 (cmd.length : Nat) - W64 ((varint cmd.length).length : Nat) - W64 1) =
          sint.nat iv - cmd.length - (varint cmd.length).length - 1 := by word
      rw [if_pos ⟨by word, by word⟩]
      wp_apply wp_store_slice_index $$ [Hsl] as Hsl
      · iframe; ipureintro; simp only [List.length_append, List.length_take]; word
      rw [show (sint.Z (iv - W64 (cmd.length : Nat) - W64 ((varint cmd.length).length : Nat) - W64 1)).toNat
          = sint.nat iv - cmd.length - (varint cmd.length).length - 1 by word]
      rw [show sint.nat iv - cmd.length - (varint cmd.length).length - 1 =
          sint.nat iv - cmd.length - (varint cmd.length).length - 1 from rfl,
        prepend_set _ _ _ _ (by omega) (by omega)]
      wp_for_post
      iframe
      iexists k', _, _
      rw [hiv2, hE]
      simp only [encBytes, List.cons_append, List.append_assoc]
      iframe
      ipureintro
      refine ⟨by omega, by word, by word, ?_⟩
      simp only [List.length_cons, List.length_append]; omega
    · -- the loop's end
      replace Hif : ¬ 0 ≤ sint.Z it := by first | exact Hif | (revert Hif; simp)
      have hk0 : k = 0 := by word
      subst hk0
      isplitl []; · ipureintro; trivial
      iexists iv
      rw [List.drop_zero] at Hk4 ⊢
      iframe
      ipureintro; exact ⟨Hk3, Hk4⟩
  · -- no commands
    have hnil : c.commands = [] := List.eq_nil_of_length_eq_zero (by word)
    iexists sl.len
    rw [hnil, List.flatMap_nil, List.append_nil, ← hL, List.take_length]
    iframe
    ipureintro; exact ⟨Hlen.2, by simp⟩
  iNamed i; iNamed Hsl; iNamed Commands; iNamed m; iNamed dAtA
  wp_join iprop(∃ (iv : w64), "i" ∷ i_ptr ↦ iv ∗
      "Hsl" ∷ sl ↦* (bs.take (sint.nat iv) ++ (encScalar 0x18 c.svrSeq.toNat ++ c.commands.flatMap (encBytes 0x22))) ∗
      "%Hiv" ∷ ⌜0 ≤ sint.Z iv ∧ sint.nat iv + (encScalar 0x18 c.svrSeq.toNat ++ c.commands.flatMap (encBytes 0x22)).length = bs.length⌝ ∗
      "SvrSeq" ∷ l.[Command, go!"SvrSeq"] ↦{dq} v.SvrSeq' ∗ "m" ∷ m_ptr ↦ l ∗
      "dAtA" ∷ dAtA_ptr ↦ sl) with [i Hsl SvrSeq m dAtA] as ⟨%iv, i, Hsl, %Hiv, SvrSeq, m, dAtA⟩
  · -- zero: nothing written
    rw [hp3] at Hif
    have hx : c.svrSeq.toNat = 0 := by rw [Hif]; rfl
    iexists iv
    rw [show encScalar 0x18 c.svrSeq.toNat = [] by rw [encScalar_eq_nil]; exact hx, List.nil_append]
    iframe
    ipureintro; exact Hiv
  · -- nonzero: varint and tag
    rw [hp3] at Hif ⊢
    have hx : c.svrSeq.toNat ≠ 0 := fun h => Hif (BitVec.eq_of_toNat_eq (by simpa using h))
    have hsc := encScalar_ne_nil (t := 0x18) (n := c.svrSeq.toNat) (by rw [Ne, encScalar_eq_nil]; exact hx)
    have hEn := hle
    rw [hcl, ← hS] at hEn
    have hvl := varint_length_le c.svrSeq.toNat 5 (by have := c.svrSeq.isLt; omega) (by omega)
    have hW' : (W64 (uint.Z c.svrSeq)).toNat = c.svrSeq.toNat := by simp [uint.Z]; have := c.svrSeq.isLt; omega
    have hlx := encScalar_length 0x18 c.svrSeq.toNat
    rw [if_neg hx] at hlx
    have hge : 1 + (varint c.svrSeq.toNat).length ≤ sint.nat iv := by
      have := Hiv.2
      try simp only [List.length_append] at this
      omega
    wp_apply (wp_encodeVarintMessage sl (bs.take (sint.nat iv) ++ (c.commands.flatMap (encBytes 0x22))) iv (W64 (uint.Z c.svrSeq))
      Hiv.1 (by rw [hW']; omega) (by simp only [List.length_append, List.length_take]; omega))
      $$ [Hsl] as Hsl
    · iexact Hsl
    rw [hW', prepend_writeAt _ _ _ _ (by omega) (by omega)]
    rw [if_pos ⟨by word, by word⟩]
    wp_apply wp_store_slice_index $$ [Hsl] as Hsl
    · iframe; ipureintro; simp only [List.length_append, List.length_take]; word
    rw [show (sint.Z (iv - W64 ((varint c.svrSeq.toNat).length : Nat) - W64 1)).toNat
        = sint.nat iv - (varint c.svrSeq.toNat).length - 1 by word,
      prepend_set _ _ _ _ (by omega) (by omega)]
    wp_join_done
    iexists _
    rw [hsc.1]
    rw [show (W8 24 : w8) = (0x18 : w8) from rfl]
    simp only [List.cons_append]
    rw [show sint.nat (iv - W64 ((varint c.svrSeq.toNat).length : Nat) - W64 1) =
      sint.nat iv - (varint c.svrSeq.toNat).length - 1 by word]
    iframe
    ipureintro
    refine ⟨by word, ?_⟩
    have := Hiv.2
    simp only [List.length_append, List.length_cons] at this ⊢
    omega
  iNamed i; iNamed Hsl; iNamed SvrSeq; iNamed m; iNamed dAtA
  wp_join iprop(∃ (iv : w64), "i" ∷ i_ptr ↦ iv ∗
      "Hsl" ∷ sl ↦* (bs.take (sint.nat iv) ++ (encScalar 0x10 c.cliSeq.toNat ++ (encScalar 0x18 c.svrSeq.toNat ++ c.commands.flatMap (encBytes 0x22)))) ∗
      "%Hiv" ∷ ⌜0 ≤ sint.Z iv ∧ sint.nat iv + (encScalar 0x10 c.cliSeq.toNat ++ (encScalar 0x18 c.svrSeq.toNat ++ c.commands.flatMap (encBytes 0x22))).length = bs.length⌝ ∗
      "CliSeq" ∷ l.[Command, go!"CliSeq"] ↦{dq} v.CliSeq' ∗ "m" ∷ m_ptr ↦ l ∗
      "dAtA" ∷ dAtA_ptr ↦ sl) with [i Hsl CliSeq m dAtA] as ⟨%iv, i, Hsl, %Hiv, CliSeq, m, dAtA⟩
  · -- zero: nothing written
    rw [hp2] at Hif
    have hx : c.cliSeq.toNat = 0 := by rw [Hif]; rfl
    iexists iv
    rw [show encScalar 0x10 c.cliSeq.toNat = [] by rw [encScalar_eq_nil]; exact hx, List.nil_append]
    iframe
    ipureintro; exact Hiv
  · -- nonzero: varint and tag
    rw [hp2] at Hif ⊢
    have hx : c.cliSeq.toNat ≠ 0 := fun h => Hif (BitVec.eq_of_toNat_eq (by simpa using h))
    have hsc := encScalar_ne_nil (t := 0x10) (n := c.cliSeq.toNat) (by rw [Ne, encScalar_eq_nil]; exact hx)
    have hEn := hle
    rw [hcl, ← hS] at hEn
    have hvl := varint_length_le c.cliSeq.toNat 5 (by have := c.cliSeq.isLt; omega) (by omega)
    have hW' : (W64 (uint.Z c.cliSeq)).toNat = c.cliSeq.toNat := by simp [uint.Z]; have := c.cliSeq.isLt; omega
    have hlx := encScalar_length 0x10 c.cliSeq.toNat
    rw [if_neg hx] at hlx
    have hge : 1 + (varint c.cliSeq.toNat).length ≤ sint.nat iv := by
      have := Hiv.2
      try simp only [List.length_append] at this
      omega
    wp_apply (wp_encodeVarintMessage sl (bs.take (sint.nat iv) ++ (encScalar 0x18 c.svrSeq.toNat ++ c.commands.flatMap (encBytes 0x22))) iv (W64 (uint.Z c.cliSeq))
      Hiv.1 (by rw [hW']; omega) (by simp only [List.length_append, List.length_take]; omega))
      $$ [Hsl] as Hsl
    · iexact Hsl
    rw [hW', prepend_writeAt _ _ _ _ (by omega) (by omega)]
    rw [if_pos ⟨by word, by word⟩]
    wp_apply wp_store_slice_index $$ [Hsl] as Hsl
    · iframe; ipureintro; simp only [List.length_append, List.length_take]; word
    rw [show (sint.Z (iv - W64 ((varint c.cliSeq.toNat).length : Nat) - W64 1)).toNat
        = sint.nat iv - (varint c.cliSeq.toNat).length - 1 by word,
      prepend_set _ _ _ _ (by omega) (by omega)]
    wp_join_done
    iexists _
    rw [hsc.1]
    rw [show (W8 16 : w8) = (0x10 : w8) from rfl]
    simp only [List.cons_append]
    rw [show sint.nat (iv - W64 ((varint c.cliSeq.toNat).length : Nat) - W64 1) =
      sint.nat iv - (varint c.cliSeq.toNat).length - 1 by word]
    iframe
    ipureintro
    refine ⟨by word, ?_⟩
    have := Hiv.2
    simp only [List.length_append, List.length_cons] at this ⊢
    omega
  iNamed i; iNamed Hsl; iNamed CliSeq; iNamed m; iNamed dAtA
  wp_join iprop(∃ (iv : w64), "i" ∷ i_ptr ↦ iv ∗
      "Hsl" ∷ sl ↦* (bs.take (sint.nat iv) ++ (encScalar 0x08 c.cliId.toNat ++ (encScalar 0x10 c.cliSeq.toNat ++ (encScalar 0x18 c.svrSeq.toNat ++ c.commands.flatMap (encBytes 0x22))))) ∗
      "%Hiv" ∷ ⌜0 ≤ sint.Z iv ∧ sint.nat iv + (encScalar 0x08 c.cliId.toNat ++ (encScalar 0x10 c.cliSeq.toNat ++ (encScalar 0x18 c.svrSeq.toNat ++ c.commands.flatMap (encBytes 0x22)))).length = bs.length⌝ ∗
      "CliId" ∷ l.[Command, go!"CliId"] ↦{dq} v.CliId' ∗ "m" ∷ m_ptr ↦ l ∗
      "dAtA" ∷ dAtA_ptr ↦ sl) with [i Hsl CliId m dAtA] as ⟨%iv, i, Hsl, %Hiv, CliId, m, dAtA⟩
  · -- zero: nothing written
    rw [hp1] at Hif
    have hx : c.cliId.toNat = 0 := by rw [Hif]; rfl
    iexists iv
    rw [show encScalar 0x08 c.cliId.toNat = [] by rw [encScalar_eq_nil]; exact hx, List.nil_append]
    iframe
    ipureintro; exact Hiv
  · -- nonzero: varint and tag
    rw [hp1] at Hif ⊢
    have hx : c.cliId.toNat ≠ 0 := fun h => Hif (BitVec.eq_of_toNat_eq (by simpa using h))
    have hsc := encScalar_ne_nil (t := 0x08) (n := c.cliId.toNat) (by rw [Ne, encScalar_eq_nil]; exact hx)
    have hEn := hle
    rw [hcl, ← hS] at hEn
    have hvl := varint_length_le c.cliId.toNat 5 (by have := c.cliId.isLt; omega) (by omega)
    have hW' : (W64 (uint.Z c.cliId)).toNat = c.cliId.toNat := by simp [uint.Z]; have := c.cliId.isLt; omega
    have hlx := encScalar_length 0x08 c.cliId.toNat
    rw [if_neg hx] at hlx
    have hge : 1 + (varint c.cliId.toNat).length ≤ sint.nat iv := by
      have := Hiv.2
      try simp only [List.length_append] at this
      omega
    wp_apply (wp_encodeVarintMessage sl (bs.take (sint.nat iv) ++ (encScalar 0x10 c.cliSeq.toNat ++ (encScalar 0x18 c.svrSeq.toNat ++ c.commands.flatMap (encBytes 0x22)))) iv (W64 (uint.Z c.cliId))
      Hiv.1 (by rw [hW']; omega) (by simp only [List.length_append, List.length_take]; omega))
      $$ [Hsl] as Hsl
    · iexact Hsl
    rw [hW', prepend_writeAt _ _ _ _ (by omega) (by omega)]
    rw [if_pos ⟨by word, by word⟩]
    wp_apply wp_store_slice_index $$ [Hsl] as Hsl
    · iframe; ipureintro; simp only [List.length_append, List.length_take]; word
    rw [show (sint.Z (iv - W64 ((varint c.cliId.toNat).length : Nat) - W64 1)).toNat
        = sint.nat iv - (varint c.cliId.toNat).length - 1 by word,
      prepend_set _ _ _ _ (by omega) (by omega)]
    wp_join_done
    iexists _
    rw [hsc.1]
    rw [show (W8 8 : w8) = (0x08 : w8) from rfl]
    simp only [List.cons_append]
    rw [show sint.nat (iv - W64 ((varint c.cliId.toNat).length : Nat) - W64 1) =
      sint.nat iv - (varint c.cliId.toNat).length - 1 by word]
    iframe
    ipureintro
    refine ⟨by word, ?_⟩
    have := Hiv.2
    simp only [List.length_append, List.length_cons] at this ⊢
    omega
  iNamed i; iNamed Hsl; iNamed CliId; iNamed m; iNamed dAtA
  have hE3 : encScalar 0x08 c.cliId.toNat ++ (encScalar 0x10 c.cliSeq.toNat ++ (encScalar 0x18 c.svrSeq.toNat ++ c.commands.flatMap (encBytes 0x22))) = encCmd c := by simp [encCmd, List.append_assoc]
  rw [hE3] at Hiv ⊢
  ihave H := typedPointsto_combine l v dq Hnn $$ [CliId CliSeq SvrSeq Commands]
  · simp only [TypedPointsto.typedPointstoDef]; iframe
  rw [show sl.len - iv = W64 ((encCmd c).length : Nat) by word,
    show bs.length - (encCmd c).length = sint.nat iv by omega]
  iapply HΦ
  iframe

set_option maxHeartbeats 1000000 in
/-- `(*Command).Marshal()`, generic in the package instance; the `isPkgInit` of `math/bits`
taken as a premise. -/
theorem Command.Marshal.wp_gen (l : Loc) (v : Command) (c : CmdV) (dq : DFrac)
    (hb : (encCmd c).length < 2 ^ 33) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.rabia.internal.message ∗
        isPkgInit (PROP := IProp GF) pkg_id.math.bits ∗ l ↦{dq} v ∗ cmdRep v c }}
      (App (Val (l @!! go.GoType.PointerType Command.ty @!! go!"Marshal")) (Val #()))
    {{ (sl : GoSlice), RET (PairV #sl #interface.nil); l ↦{dq} v ∗ sl ↦* encCmd c }} := by
  wp_start as ⟨Hl, #Hrep⟩
  wp_auto
  wp_apply (Command.Size.wp_bounded l v c dq hb) $$ [Hl] as Hl
  · iframe; iexact Hrep
  wp_apply (wp_slice_make2 (V := w8) (W64 ((encCmd c).length : Nat))) as %sl ⟨Hsl, -⟩
  · ipureintro; word
  ihave %Hsll := ownSlice_len _ _ _ $$ Hsl
  ihave %Hslw := ownSlice_wf _ _ _ $$ Hsl
  have hsllen : sl.len = W64 ((encCmd c).length : Nat) := by
    simp only [List.length_replicate] at Hsll; word
  rw [if_pos ⟨by word, by word, by word⟩, ← hsllen, ← slice_slice_trivial]
  wp_auto
  wp_apply (Command.MarshalToSizedBuffer.wp_bounded l v c dq sl
    (List.replicate (sint.nat sl.len) (Perennial.zero_val w8)) hb
    (by rw [List.length_replicate, hsllen]; word)) $$ [Hl Hsl]
    as ⟨Hl, Hsl⟩
  · iframe; iexact Hrep
  simp only [List.length_replicate, show sint.nat sl.len = (encCmd c).length
    by rw [hsllen]; word, Nat.sub_self, List.take_zero, List.nil_append]
  rw [if_pos ⟨by word, by word, by word⟩, ← hsllen, ← slice_slice_trivial]
  wp_auto
  wp_end

end proof
end Perennial.rabia.internal.message

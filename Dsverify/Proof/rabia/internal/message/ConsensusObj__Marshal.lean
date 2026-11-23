/-
(Ported from dsverify-lab `examples/rabia/proof/Proof/rabia/internal/message/ConsensusObj__Marshal.lean`, run `rabia-r1wake-1`.)

`(*ConsensusObj).Size`, `(*ConsensusObj).MarshalToSizedBuffer` (message.pb.go 570-646, 859-898):
the encoder writes `encObj o` (prover C1b).
-/
module

public import Dsverify.Proof.rabia.internal.message.Command__Marshal
public import Dsverify.Proof.rabia.internal.message.ObjWire

@[expose] public section

namespace Perennial.rabia.model

/-- The payload of a packed field. -/
abbrev packedPay (ns : List w32) : List w8 := ns.flatMap fun n => varint n.toNat

theorem encPacked_length (t : w8) (ns : List w32) :
    (encPacked t ns).length =
      if ns = [] then 0 else 1 + (varint (packedPay ns).length).length + (packedPay ns).length := by
  unfold encPacked; split <;> simp [encBytes]; omega

theorem varint_w32_length (x : w32) : 1 ≤ (varint x.toNat).length ∧ (varint x.toNat).length ≤ 5 :=
  ⟨varint_length_pos _, varint_length_le _ _ (by have := x.isLt; omega) (by omega)⟩

theorem packedPay_length (ns : List w32) :
    ns.length ≤ (packedPay ns).length ∧ (packedPay ns).length ≤ 5 * ns.length := by
  induction ns with
  | nil => simp
  | cons x ns ih =>
    have := varint_w32_length x
    simp only [packedPay, List.flatMap_cons, List.length_append, List.length_cons] at ih ⊢
    omega

theorem packedPay_take_succ (ns : List w32) (k : Nat) (h : k < ns.length) :
    packedPay (ns.take (k + 1)) = packedPay (ns.take k) ++ varint ns[k].toNat := by
  unfold packedPay
  rw [List.take_add_one, List.getElem?_eq_getElem h]
  simp only [Option.toList_some, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
    List.append_nil]

theorem writeAt_prefix (P Z X : List w8) :
    writeAt (P ++ Z.drop P.length) P.length X = P ++ X ++ Z.drop (P.length + X.length) := by
  unfold writeAt
  have h1 : (P ++ Z.drop P.length).take P.length = P := by simp
  have h2 : (P ++ Z.drop P.length).drop (P.length + X.length) = Z.drop (P.length + X.length) := by
    rw [List.drop_append]; simp [List.drop_drop]
  rw [h1, h2]

theorem encObj_length (o : ObjV) : (encObj o).length =
    0 + (encScalar 0x08 o.proId.toNat).length + (encScalar 0x10 o.proSeq.toNat).length +
      (encScalar 0x18 o.svrSeq.toNat).length + (if o.isNull then 2 else 0) +
      (encPacked 0x2a o.cliIds).length + (encPacked 0x32 o.cliSeqs).length +
      (o.commands.flatMap (encBytes 0x3a)).length := by
  simp only [encObj, List.length_append]; split <;> simp <;> omega

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
/-- `(*ConsensusObj).Size()`: the length of the encoding. -/
theorem ConsensusObj.Size.wp_bounded (l : Loc) (v : ConsensusObj) (o : ObjV) (dq : DFrac)
    (hb : (encObj o).length < 2 ^ 32) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.rabia.internal.message ∗
        isPkgInit (PROP := IProp GF) pkg_id.math.bits ∗ l ↦{dq} v ∗ objRep v o }}
      (App (Val (l @!! go.GoType.PointerType ConsensusObj.ty @!! go!"Size")) (Val #()))
    {{ RET #(W64 (encObj o).length); l ↦{dq} v }} := by
  wp_start as ⟨Hl, #Hrep⟩
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hl
  unfold objRep
  icases Hrep with ⟨%Hp, #HcliIds, #HcliSeqs, #Hcmds⟩
  obtain ⟨hp1, hp2, hp3, hp4⟩ := Hp
  icases typedPointsto_split _ _ _ $$ Hl with Hl
  simp only [TypedPointsto.typedPointstoDef]
  icases Hl with ⟨ProId, ProSeq, SvrSeq, IsNull, CliIds, CliSeqs, Commands, -⟩
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
  have hcl := encObj_length o
  wp_join iprop("n" ∷ n_ptr ↦ W64 ((0 + (encScalar 0x08 o.proId.toNat).length : Nat) : Int) ∗ "m" ∷ m_ptr ↦ l ∗
      "ProId" ∷ l.[ConsensusObj, go!"ProId"] ↦{dq} v.ProId') with [n m ProId] as ⟨n, m, ProId⟩
  · rw [hp1] at Hif; rw [Hif, ← hsc0 0x08 (0)]
    iframe
  · wp_apply wp_sovMessage
    · iexact Hpkg2
    rw [hp1] at Hif ⊢
    rw [hW, hsc 0x08 o.proId (0) (by omega) Hif]
    wp_join_done
  iNamed n; iNamed m; iNamed ProId
  wp_join iprop("n" ∷ n_ptr ↦ W64 ((0 + (encScalar 0x08 o.proId.toNat).length + (encScalar 0x10 o.proSeq.toNat).length : Nat) : Int) ∗ "m" ∷ m_ptr ↦ l ∗
      "ProSeq" ∷ l.[ConsensusObj, go!"ProSeq"] ↦{dq} v.ProSeq') with [n m ProSeq] as ⟨n, m, ProSeq⟩
  · rw [hp2] at Hif; rw [Hif, ← hsc0 0x10 (0 + (encScalar 0x08 o.proId.toNat).length)]
    iframe
  · wp_apply wp_sovMessage
    · iexact Hpkg2
    rw [hp2] at Hif ⊢
    rw [hW, hsc 0x10 o.proSeq (0 + (encScalar 0x08 o.proId.toNat).length) (by omega) Hif]
    wp_join_done
  iNamed n; iNamed m; iNamed ProSeq
  wp_join iprop("n" ∷ n_ptr ↦ W64 ((0 + (encScalar 0x08 o.proId.toNat).length + (encScalar 0x10 o.proSeq.toNat).length + (encScalar 0x18 o.svrSeq.toNat).length : Nat) : Int) ∗ "m" ∷ m_ptr ↦ l ∗
      "SvrSeq" ∷ l.[ConsensusObj, go!"SvrSeq"] ↦{dq} v.SvrSeq') with [n m SvrSeq] as ⟨n, m, SvrSeq⟩
  · rw [hp3] at Hif; rw [Hif, ← hsc0 0x18 (0 + (encScalar 0x08 o.proId.toNat).length + (encScalar 0x10 o.proSeq.toNat).length)]
    iframe
  · wp_apply wp_sovMessage
    · iexact Hpkg2
    rw [hp3] at Hif ⊢
    rw [hW, hsc 0x18 o.svrSeq (0 + (encScalar 0x08 o.proId.toNat).length + (encScalar 0x10 o.proSeq.toNat).length) (by omega) Hif]
    wp_join_done
  iNamed n; iNamed m; iNamed SvrSeq
  obtain ⟨S3, hS3⟩ : ∃ S3, 0 + (encScalar 0x08 o.proId.toNat).length + (encScalar 0x10 o.proSeq.toNat).length +
      (encScalar 0x18 o.svrSeq.toNat).length = S3 := ⟨_, rfl⟩
  rw [hS3] at hcl ⊢
  wp_join iprop("n" ∷ n_ptr ↦ W64 ((S3 + (if o.isNull then 2 else 0) : Nat) : Int) ∗ "m" ∷ m_ptr ↦ l ∗
      "IsNull" ∷ l.[ConsensusObj, go!"IsNull"] ↦{dq} v.IsNull') at next with [n m IsNull] as ⟨n, m, IsNull⟩
  · rw [hp4]
    cases hnull : o.isNull
    · wp_auto
      simp only [Bool.false_eq_true, ite_false, Nat.add_zero]
      wp_join_done
    · wp_auto
      rw [show W64 ((S3 + if true = true then 2 else 0 : Nat) : Int) = W64 (S3 : Nat) + W64 2 by
        simp only [ite_true]; word]
      wp_join_done
  iNamed n; iNamed m; iNamed IsNull
  obtain ⟨S4, hS4⟩ : ∃ S4, S3 + (if o.isNull then 2 else 0) = S4 := ⟨_, rfl⟩
  rw [hS4] at hcl ⊢
  ihave %HcliIdsl := ownSlice_len _ _ _ $$ HcliIds
  wp_join iprop("n" ∷ n_ptr ↦ W64 ((S4 + (encPacked 0x2a o.cliIds).length : Nat) : Int) ∗ "m" ∷ m_ptr ↦ l ∗
      "l" ∷ (∃ lv : w64, l_ptr ↦ lv) ∗
      "CliIds" ∷ l.[ConsensusObj, go!"CliIds"] ↦{dq} v.CliIds') with [n m l CliIds] as ⟨n, m, l, CliIds⟩
  · ihave HI : (∃ (i : w64) (ev : w32), "i" ∷ i_ptr ↦ i ∗
        "l" ∷ l_ptr ↦ W64 (((o.cliIds.take (sint.nat i)).flatMap fun n => varint n.toNat).length : Nat) ∗
        "e" ∷ e_ptr ↦ ev ∗
        "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.nat i ≤ o.cliIds.length⌝ : IProp GF) $$ [i l e]
    · iexists _, _
      iframe
      simp only [show sint.nat (W64 0) = 0 from rfl, List.take_zero, List.flatMap_nil,
        List.length_nil]
      iframe
      ipureintro; exact ⟨by decide, by omega⟩
    wp_for HI
    have hPle : (packedPay o.cliIds).length ≤ (encObj o).length := by
      have := encPacked_length 0x2a o.cliIds
      have hne : o.cliIds ≠ [] := by
        intro h; rw [h] at HcliIdsl; simp at HcliIdsl; word
      rw [if_neg hne] at this; omega
    wp_if_destruct
    · obtain ⟨Hi1, Hi2⟩ := Hi
      have hilt : sint.nat i < o.cliIds.length := by word
      have hi1 : sint.nat (i + W64 1) = sint.nat i + 1 := by word
      have hfin : 0 ≤ sint.Z (i + W64 1) ∧ sint.nat i + 1 ≤ o.cliIds.length := ⟨by word, by word⟩
      list_elem o.cliIds (sint.nat i) as x
      rw [if_pos ⟨Hi1, by word⟩]
      wp_apply wp_load_slice_index _ (sint.Z i) o.cliIds DFrac.discard x Hi1 $$ [] as -
      · isplitl []; · iexact HcliIds
        ipureintro; rw [show (sint.Z i).toNat = sint.nat i by word]; exact Hx_lookup
      wp_apply wp_sovMessage
      · iexact Hpkg2
      have hxi : o.cliIds[sint.nat i] = x := by
        rw [List.getElem?_eq_some_iff] at Hx_lookup; exact Hx_lookup.2
      have hP := flatMap_take_succ (fun n : w32 => varint n.toNat) o.cliIds (sint.nat i) hilt
      rw [hxi] at hP
      have hPle2 : ((o.cliIds.take (sint.nat i + 1)).flatMap fun n : w32 => varint n.toNat).length ≤
          (packedPay o.cliIds).length := flatMap_take_le _ _ _
      rw [hW]
      wp_for_post
      iframe
      iexists _, _
      iframe
      rw [hi1]
      rw [show W64 ((((o.cliIds.take (sint.nat i)).flatMap fun n : w32 => varint n.toNat).length : Nat) : Int) +
          W64 ((varint x.toNat).length : Nat) =
          W64 ((((o.cliIds.take (sint.nat i + 1)).flatMap fun n : w32 => varint n.toNat).length : Nat) : Int) by
        rw [hP]; word]
      iframe
      ipureintro; exact hfin
    · obtain ⟨Hi1, Hi2⟩ := Hi
      rw [show sint.nat i = o.cliIds.length by word, List.take_length]
      have hne : o.cliIds ≠ [] := by
        intro h; rw [h] at HcliIdsl; simp at HcliIdsl; word
      have hEP := encPacked_length 0x2a o.cliIds
      rw [if_neg hne] at hEP
      have hvl := varint_length_le (packedPay o.cliIds).length 5 (by omega) (by omega)
      generalize hPdef : (o.cliIds.flatMap fun n : w32 => varint n.toNat).length = P at hEP hvl hPle ⊢
      wp_apply wp_sovMessage
      · iexact Hpkg2
      rw [show (W64 ((P : Nat) : Int)).toNat = P by word]
      rw [show W64 (S4 : Nat) + (W64 1 + W64 ((varint P).length : Nat) + W64 ((P : Nat) : Int)) =
          W64 ((S4 + (encPacked 0x2a o.cliIds).length : Nat) : Int) by rw [hEP]; word]
      wp_join_done
      iframe; iexists _; iframe
  · have hnil : o.cliIds = [] := by
      apply List.eq_nil_of_length_eq_zero; word
    rw [hnil, show (encPacked 0x2a ([] : List w32)).length = 0 from rfl, Nat.add_zero]
    iframe
    iexists _
    iframe
  iNamed n; iNamed m; iNamed CliIds
  icases l with ⟨%lv0, l⟩
  obtain ⟨S5, hS5⟩ : ∃ S5, S4 + (encPacked 0x2a o.cliIds).length = S5 := ⟨_, rfl⟩
  rw [hS5] at hcl ⊢
  ihave %HcliSeqsl := ownSlice_len _ _ _ $$ HcliSeqs
  wp_join iprop("n" ∷ n_ptr ↦ W64 ((S5 + (encPacked 0x32 o.cliSeqs).length : Nat) : Int) ∗ "m" ∷ m_ptr ↦ l ∗
      "l" ∷ (∃ lv : w64, l_ptr ↦ lv) ∗
      "CliSeqs" ∷ l.[ConsensusObj, go!"CliSeqs"] ↦{dq} v.CliSeqs') with [n m l CliSeqs] as ⟨n, m, l, CliSeqs⟩
  · ihave HI : (∃ (i : w64) (ev : w32), "i" ∷ i_ptr ↦ i ∗
        "l" ∷ l_ptr ↦ W64 (((o.cliSeqs.take (sint.nat i)).flatMap fun n => varint n.toNat).length : Nat) ∗
        "e" ∷ e_ptr ↦ ev ∗
        "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.nat i ≤ o.cliSeqs.length⌝ : IProp GF) $$ [i l e]
    · iexists _, _
      iframe
      simp only [show sint.nat (W64 0) = 0 from rfl, List.take_zero, List.flatMap_nil,
        List.length_nil]
      iframe
      ipureintro; exact ⟨by decide, by omega⟩
    wp_for HI
    have hPle : (packedPay o.cliSeqs).length ≤ (encObj o).length := by
      have := encPacked_length 0x32 o.cliSeqs
      have hne : o.cliSeqs ≠ [] := by
        intro h; rw [h] at HcliSeqsl; simp at HcliSeqsl; word
      rw [if_neg hne] at this; omega
    wp_if_destruct
    · obtain ⟨Hi1, Hi2⟩ := Hi
      have hilt : sint.nat i < o.cliSeqs.length := by word
      have hi1 : sint.nat (i + W64 1) = sint.nat i + 1 := by word
      have hfin : 0 ≤ sint.Z (i + W64 1) ∧ sint.nat i + 1 ≤ o.cliSeqs.length := ⟨by word, by word⟩
      list_elem o.cliSeqs (sint.nat i) as x
      rw [if_pos ⟨Hi1, by word⟩]
      wp_apply wp_load_slice_index _ (sint.Z i) o.cliSeqs DFrac.discard x Hi1 $$ [] as -
      · isplitl []; · iexact HcliSeqs
        ipureintro; rw [show (sint.Z i).toNat = sint.nat i by word]; exact Hx_lookup
      wp_apply wp_sovMessage
      · iexact Hpkg2
      have hxi : o.cliSeqs[sint.nat i] = x := by
        rw [List.getElem?_eq_some_iff] at Hx_lookup; exact Hx_lookup.2
      have hP := flatMap_take_succ (fun n : w32 => varint n.toNat) o.cliSeqs (sint.nat i) hilt
      rw [hxi] at hP
      have hPle2 : ((o.cliSeqs.take (sint.nat i + 1)).flatMap fun n : w32 => varint n.toNat).length ≤
          (packedPay o.cliSeqs).length := flatMap_take_le _ _ _
      rw [hW]
      wp_for_post
      iframe
      iexists _, _
      iframe
      rw [hi1]
      rw [show W64 ((((o.cliSeqs.take (sint.nat i)).flatMap fun n : w32 => varint n.toNat).length : Nat) : Int) +
          W64 ((varint x.toNat).length : Nat) =
          W64 ((((o.cliSeqs.take (sint.nat i + 1)).flatMap fun n : w32 => varint n.toNat).length : Nat) : Int) by
        rw [hP]; word]
      iframe
      ipureintro; exact hfin
    · obtain ⟨Hi1, Hi2⟩ := Hi
      rw [show sint.nat i = o.cliSeqs.length by word, List.take_length]
      have hne : o.cliSeqs ≠ [] := by
        intro h; rw [h] at HcliSeqsl; simp at HcliSeqsl; word
      have hEP := encPacked_length 0x32 o.cliSeqs
      rw [if_neg hne] at hEP
      have hvl := varint_length_le (packedPay o.cliSeqs).length 5 (by omega) (by omega)
      generalize hPdef : (o.cliSeqs.flatMap fun n : w32 => varint n.toNat).length = P at hEP hvl hPle ⊢
      wp_apply wp_sovMessage
      · iexact Hpkg2
      rw [show (W64 ((P : Nat) : Int)).toNat = P by word]
      rw [show W64 (S5 : Nat) + (W64 1 + W64 ((varint P).length : Nat) + W64 ((P : Nat) : Int)) =
          W64 ((S5 + (encPacked 0x32 o.cliSeqs).length : Nat) : Int) by rw [hEP]; word]
      wp_join_done
      iframe; iexists _; iframe
  · have hnil : o.cliSeqs = [] := by
      apply List.eq_nil_of_length_eq_zero; word
    rw [hnil, show (encPacked 0x32 ([] : List w32)).length = 0 from rfl, Nat.add_zero]
    iframe
    iexists _
    iframe
  iNamed n; iNamed m; iNamed CliSeqs
  icases l with ⟨%lv1, l⟩
  obtain ⟨S, hS⟩ : ∃ S, S5 + (encPacked 0x32 o.cliSeqs).length = S := ⟨_, rfl⟩
  rw [hS] at hcl ⊢
  ihave %Hcl := ownSlice_len _ _ _ $$ Hcmds
  wp_if_destruct
  · -- the commands
    ihave HI : (∃ (i : w64) (sv : GoString) (lv : w64), "i" ∷ i_ptr ↦ i ∗
        "n" ∷ n_ptr ↦ W64 ((S + ((o.commands.take (sint.nat i)).flatMap (encBytes 0x3a)).length : Nat) : Int) ∗
        "s" ∷ s_ptr ↦ sv ∗ "l" ∷ l_ptr ↦ lv ∗
        "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.nat i ≤ o.commands.length⌝ : IProp GF) $$ [i n s l]
    · iexists _, _, _
      iframe
      simp only [show sint.nat (W64 0) = 0 from rfl, List.take_zero, List.flatMap_nil,
        List.length_nil, Nat.add_zero]
      iframe
      ipureintro; exact ⟨by decide, by omega⟩
    wp_for HI
    wp_if_destruct
    · obtain ⟨Hi1, Hi2⟩ := Hi
      have hilt : sint.nat i < o.commands.length := by word
      rw [if_pos ⟨Hi1, by word⟩]
      list_elem o.commands (sint.nat i) as cmd
      wp_apply wp_load_slice_index _ (sint.Z i) o.commands DFrac.discard cmd Hi1 $$ [] as -
      · isplitl []; · iexact Hcmds
        ipureintro; rw [show (sint.Z i).toNat = sint.nat i by word]; exact Hcmd_lookup
      wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %Hslen
      wp_apply wp_sovMessage
      · iexact Hpkg2
      have hcmdi : o.commands[sint.nat i] = cmd := by
        rw [List.getElem?_eq_some_iff] at Hcmd_lookup; exact Hcmd_lookup.2
      have hP := flatMap_take_succ (encBytes 0x3a) o.commands (sint.nat i) hilt
      rw [hcmdi, encBytes_length] at hP
      have hPle : ((o.commands.take (sint.nat i + 1)).flatMap (encBytes 0x3a)).length ≤
          (o.commands.flatMap (encBytes 0x3a)).length := by
        have := flatMap_take_le (encBytes 0x3a) o.commands (sint.nat i + 1); omega
      have hvl := varint_length_le cmd.length 10 (by omega) (by omega)
      have hW2 : (W64 (cmd.length : Nat)).toNat = cmd.length := by word
      rw [hW2]
      wp_for_post
      iframe
      iexists _, _, _
      iframe
      rw [show sint.nat (i + W64 1) = sint.nat i + 1 by word]
      rw [show W64 ((S + ((o.commands.take (sint.nat i)).flatMap (encBytes 0x3a)).length : Nat) : Int) +
          (W64 1 + W64 (cmd.length : Nat) + W64 ((varint cmd.length).length : Nat)) =
          W64 ((S + ((o.commands.take (sint.nat i + 1)).flatMap (encBytes 0x3a)).length : Nat) : Int) by
        rw [hP]; word]
      iframe
      ipureintro; exact ⟨by word, by word⟩
    · -- the loop's end
      obtain ⟨Hi1, Hi2⟩ := Hi
      rw [show sint.nat i = o.commands.length by word, List.take_length, ← hcl]
      ihave H := typedPointsto_combine l v dq Hnn $$ [ProId ProSeq SvrSeq IsNull CliIds CliSeqs Commands]
      · simp only [TypedPointsto.typedPointstoDef]; iframe
      wp_end
  · -- no commands
    have hnil : o.commands = [] := by
      apply List.eq_nil_of_length_eq_zero; word
    rw [hnil, List.flatMap_nil, List.length_nil, Nat.add_zero] at hcl
    rw [← hcl]
    ihave H := typedPointsto_combine l v dq Hnn $$ [ProId ProSeq SvrSeq IsNull CliIds CliSeqs Commands]
    · simp only [TypedPointsto.typedPointstoDef]; iframe
    wp_end



set_option maxHeartbeats 4000000 in
/-- `(*ConsensusObj).MarshalToSizedBuffer(dAtA)`: the encoding written at the end of `dAtA`. -/
theorem ConsensusObj.MarshalToSizedBuffer.wp_bounded (l : Loc) (v : ConsensusObj) (o : ObjV)
    (dq : DFrac) (sl : GoSlice) (bs : List w8) (hb : (encObj o).length < 2 ^ 32)
    (hle : (encObj o).length ≤ bs.length) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.rabia.internal.message ∗
        isPkgInit (PROP := IProp GF) pkg_id.math.bits ∗ l ↦{dq} v ∗ objRep v o ∗ sl ↦* bs }}
      (App (Val (l @!! go.GoType.PointerType ConsensusObj.ty @!! go!"MarshalToSizedBuffer"))
        (Val #sl))
    {{ RET (PairV #(W64 (encObj o).length) #interface.nil);
        l ↦{dq} v ∗ sl ↦* (bs.take (bs.length - (encObj o).length) ++ encObj o) }} := by
  wp_start as ⟨Hl, #Hrep, Hsl⟩
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hl
  ihave %Hlen := ownSlice_len _ _ _ $$ Hsl
  unfold objRep
  icases Hrep with ⟨%Hp, #HcliIds, #HcliSeqs, #Hcmds⟩
  obtain ⟨hp1, hp2, hp3, hp4⟩ := Hp
  icases typedPointsto_split _ _ _ $$ Hl with Hl
  simp only [TypedPointsto.typedPointstoDef]
  icases Hl with ⟨ProId, ProSeq, SvrSeq, IsNull, CliIds, CliSeqs, Commands, -⟩
  ihave %Hcl := ownSlice_len _ _ _ $$ Hcmds
  have hcl := encObj_length o
  obtain ⟨S, hS⟩ : ∃ S, 0 + (encScalar 0x08 o.proId.toNat).length + (encScalar 0x10 o.proSeq.toNat).length +
      (encScalar 0x18 o.svrSeq.toNat).length + (if o.isNull then 2 else 0) +
      (encPacked 0x2a o.cliIds).length + (encPacked 0x32 o.cliSeqs).length = S := ⟨_, rfl⟩
  rw [hS] at hcl
  have hL := Hlen.1
  wp_auto
  wp_join iprop(∃ (iv : w64), "i" ∷ i_ptr ↦ iv ∗
      "Hsl" ∷ sl ↦* (bs.take (sint.nat iv) ++ o.commands.flatMap (encBytes 0x3a)) ∗
      "%Hiv" ∷ ⌜0 ≤ sint.Z iv ∧ sint.nat iv + (o.commands.flatMap (encBytes 0x3a)).length = bs.length⌝ ∗
      "Commands" ∷ l.[ConsensusObj, go!"Commands"] ↦{dq} v.Commands' ∗ "m" ∷ m_ptr ↦ l ∗
      "dAtA" ∷ dAtA_ptr ↦ sl) with [i Hsl Commands m dAtA] as ⟨%iv, i, Hsl, %Hiv, Commands, m, dAtA⟩
  · -- the commands, back to front
    ihave HI : (∃ (k : Nat) (it iv : w64), "iNdEx" ∷ iNdEx_ptr ↦ it ∗ "i" ∷ i_ptr ↦ iv ∗
        "Hsl" ∷ sl ↦* (bs.take (sint.nat iv) ++ (o.commands.drop k).flatMap (encBytes 0x3a)) ∗
        "%Hk" ∷ ⌜k ≤ o.commands.length ∧ sint.Z it = (k : Int) - 1 ∧ 0 ≤ sint.Z iv ∧
          sint.nat iv + ((o.commands.drop k).flatMap (encBytes 0x3a)).length = bs.length⌝ : IProp GF)
        $$ [iNdEx i Hsl]
    · iexists o.commands.length, _, _
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
      have hk' : k' < o.commands.length := by omega
      list_elem o.commands k' as cmd
      have hcmd : o.commands[k'] = cmd := by
        rw [List.getElem?_eq_some_iff] at Hcmd_lookup; exact Hcmd_lookup.2
      have hE : (o.commands.drop k').flatMap (encBytes 0x3a) =
          encBytes 0x3a cmd ++ (o.commands.drop (k' + 1)).flatMap (encBytes 0x3a) := by
        rw [List.drop_eq_getElem_cons hk', hcmd]; simp
      generalize hEdef : (o.commands.drop (k' + 1)).flatMap (encBytes 0x3a) = E at Hk4 hE ⊢
      have hEl := congrArg List.length hE
      simp only [List.length_append, encBytes_length] at hEl
      have hEle : ((o.commands.drop k').flatMap (encBytes 0x3a)).length ≤
          (o.commands.flatMap (encBytes 0x3a)).length := by
        conv => rhs; rw [← List.take_append_drop k' o.commands]
        simp only [List.flatMap_append, List.length_append]; omega
      have hvl := varint_length_le cmd.length 10 (by omega) (by omega)
      rw [if_pos ⟨by word, by word⟩]
      wp_apply wp_load_slice_index _ (sint.Z it) o.commands DFrac.discard cmd (by word) $$ [] as -
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
      wp_apply wp_load_slice_index _ (sint.Z it) o.commands DFrac.discard cmd (by word) $$ [] as -
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
      wp_apply wp_load_slice_index _ (sint.Z it) o.commands DFrac.discard cmd (by word) $$ [] as -
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
    have hnil : o.commands = [] := List.eq_nil_of_length_eq_zero (by word)
    iexists sl.len
    rw [hnil, List.flatMap_nil, List.append_nil, ← hL, List.take_length]
    iframe
    ipureintro; exact ⟨Hlen.2, by simp⟩
  iNamed i; iNamed Hsl; iNamed Commands; iNamed m; iNamed dAtA
  obtain ⟨E, hE⟩ : ∃ E, o.commands.flatMap (encBytes 0x3a) = E := ⟨_, rfl⟩
  rw [hE] at hcl Hiv ⊢
  ihave %HcliSeqsl := ownSlice_len _ _ _ $$ HcliSeqs
  wp_join iprop(∃ (iv : w64), "i" ∷ i_ptr ↦ iv ∗
      "Hsl" ∷ sl ↦* (bs.take (sint.nat iv) ++ (encPacked 0x32 o.cliSeqs ++ E)) ∗
      "%Hiv" ∷ ⌜0 ≤ sint.Z iv ∧ sint.nat iv + (encPacked 0x32 o.cliSeqs ++ E).length = bs.length⌝ ∗
      "CliSeqs" ∷ l.[ConsensusObj, go!"CliSeqs"] ↦{dq} v.CliSeqs' ∗ "m" ∷ m_ptr ↦ l ∗
      "dAtA" ∷ dAtA_ptr ↦ sl) with [i Hsl CliSeqs m dAtA] as ⟨%iv, i, Hsl, %Hiv, CliSeqs, m, dAtA⟩
  · have hne : o.cliSeqs ≠ [] := by
      intro h; rw [h] at HcliSeqsl; simp at HcliSeqsl; word
    have hPL := packedPay_length o.cliSeqs
    have hEP := encPacked_length 0x32 o.cliSeqs
    rw [if_neg hne] at hEP
    have hlenS : sint.nat v.CliSeqs'.len = o.cliSeqs.length := by word
    have hnsl : o.cliSeqs.length < 2 ^ 32 := by omega
    have hlenZ : sint.Z v.CliSeqs'.len < 2 ^ 32 := by word
    have h10 : sint.nat (v.CliSeqs'.len * W64 10) = 10 * o.cliSeqs.length := by word
    irename i => Hii
    wp_apply (wp_slice_make2 (V := w8) (v.CliSeqs'.len * W64 10)) as %d2 ⟨Hd2, -⟩
    · ipureintro; word
    rw [h10]
    rename_i ip
    obtain ⟨Z, hZ⟩ : ∃ Z, List.replicate (10 * o.cliSeqs.length) (Perennial.zero_val w8) = Z := ⟨_, rfl⟩
    have hZl : Z.length = 10 * o.cliSeqs.length := by rw [← hZ, List.length_replicate]
    rw [hZ, show (Perennial.zero_val w64) = W64 ((0 : Nat) : Int) from rfl]
    ihave HI : (∃ (k : w64) (nv : w32), "i" ∷ i_ptr ↦ k ∗
        "j1" ∷ j1_ptr ↦ W64 ((packedPay (o.cliSeqs.take (sint.nat k))).length : Nat) ∗
        "num" ∷ num_ptr ↦ nv ∗
        "Hd2" ∷ d2 ↦* (packedPay (o.cliSeqs.take (sint.nat k)) ++
          Z.drop (packedPay (o.cliSeqs.take (sint.nat k))).length) ∗
        "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.nat k ≤ o.cliSeqs.length⌝ : IProp GF) $$ [i j1 num Hd2]
    · iexists (W64 0), _
      simp only [show sint.nat (W64 0) = 0 from rfl, List.take_zero, packedPay, List.flatMap_nil,
        List.length_nil, List.drop_zero, List.nil_append]
      iframe
      ipureintro; exact ⟨by decide, by omega⟩
    wp_for HI
    wp_if_destruct
    · obtain ⟨Hk1, Hk2⟩ := Hk
      have hklt : sint.nat k < o.cliSeqs.length := by word
      have hk1 : sint.nat (k + W64 1) = sint.nat k + 1 := by word
      have hkfin : 0 ≤ sint.Z (k + W64 1) ∧ sint.nat k + 1 ≤ o.cliSeqs.length := ⟨by word, by word⟩
      list_elem o.cliSeqs (sint.nat k) as x
      have hxk : o.cliSeqs[sint.nat k] = x := by
        rw [List.getElem?_eq_some_iff] at Hx_lookup; exact Hx_lookup.2
      have hPs := packedPay_take_succ o.cliSeqs (sint.nat k) hklt
      rw [hxk] at hPs
      clear hxk
      have hPsl := packedPay_length (o.cliSeqs.take (sint.nat k + 1))
      rw [hPs] at hPsl
      simp only [List.length_append, List.length_take, Nat.min_eq_left hklt] at hPsl
      rw [if_pos ⟨Hk1, by word⟩]
      wp_apply wp_load_slice_index _ (sint.Z k) o.cliSeqs DFrac.discard x Hk1 $$ [] as -
      · isplitl []; · iexact HcliSeqs
        ipureintro; rw [show (sint.Z k).toNat = sint.nat k by word]; exact Hx_lookup
      ihave %Hd2l := ownSlice_len _ _ _ $$ Hd2
      obtain ⟨Pk, hPk⟩ : ∃ Pk, packedPay (o.cliSeqs.take (sint.nat k)) = Pk := ⟨_, rfl⟩
      rw [hPk] at hPs hPsl Hd2l ⊢
      have hPkZ : Pk.length + (varint x.toNat).length ≤ Z.length := by omega
      have hd2len : (Pk ++ Z.drop Pk.length).length = Z.length := by simp; omega
      have hd2 : sint.nat d2.len = Z.length := by rw [← Hd2l.1, hd2len]
      ihave HJ : (∃ (j : Nat) (vv : w32), "num" ∷ num_ptr ↦ vv ∗
          "j1" ∷ j1_ptr ↦ W64 ((Pk.length + j : Nat) : Int) ∗
          "Hd2" ∷ d2 ↦* writeAt (Pk ++ Z.drop Pk.length) Pk.length ((varint x.toNat).take j) ∗
          "%Hj" ∷ ⌜vv.toNat = x.toNat / 2 ^ (7 * j) ∧
            (varint x.toNat).drop j = varint (x.toNat / 2 ^ (7 * j))⌝ : IProp GF) $$ [num j1 Hd2]
      · iexists 0, x
        simp only [Nat.add_zero, List.take_zero, writeAt_nil]
        iframe
        ipureintro; simp
      wp_for HJ
      obtain ⟨Hj1, Hj4⟩ := Hj
      have hjk : j < (varint x.toNat).length := by
        apply Nat.lt_of_not_le; intro hj
        rw [List.drop_eq_nil_of_le hj] at Hj4
        exact varint_ne_nil _ Hj4.symm
      have hwl : (writeAt (Pk ++ Z.drop Pk.length) Pk.length ((varint x.toNat).take j)).length = Z.length := by
        rw [writeAt_length _ _ _ (by simp; omega), hd2len]
      wp_if_destruct
      · have hge : ¬ x.toNat / 2 ^ (7 * j) < 128 := by rw [← Hj1]; word
        rw [varint_ge _ hge] at Hj4
        rw [if_pos ⟨by word, by word⟩]
        rw [byte_cont, show (W64 (uint.Z vv)).toNat = vv.toNat by simp [uint.Z]; have := vv.isLt; omega, Hj1]
        wp_apply wp_store_slice_index $$ [Hd2] as Hd2
        · iframe; ipureintro; word
        wp_for_post
        iframe
        iexists j + 1, _
        rw [show (sint.Z (W64 ((Pk.length + j : Nat) : Int))).toNat =
            Pk.length + ((varint x.toNat).take j).length by
          rw [List.length_take, Nat.min_eq_left (by omega)]; word]
        rw [writeAt_snoc _ _ _ _ (by rw [List.length_take, Nat.min_eq_left (by omega)]; omega),
          ← take_succ_of_drop _ _ _ _ Hj4]
        rw [show W64 ((Pk.length + j : Nat) : Int) + W64 1 = W64 ((Pk.length + (j + 1) : Nat) : Int) by
          word]
        iframe
        ipureintro
        refine ⟨?_, ?_⟩
        · rw [div_pow_succ]
          have : (vv >>> W64 7).toNat = vv.toNat / 128 := by
            rw [BitVec.ushiftRight_eq', BitVec.toNat_ushiftRight, show (W64 7).toNat = 7 from rfl,
              Nat.shiftRight_eq_div_pow]
          rw [this, Hj1]
        · rw [div_pow_succ, ← List.drop_drop, Hj4]; rfl
      · have hlt : x.toNat / 2 ^ (7 * j) < 128 := by rw [← Hj1]; word
        rw [varint_lt _ hlt] at Hj4
        have hb8 : W8 (uint.Z vv) = BitVec.ofNat 8 vv.toNat := by
          apply BitVec.eq_of_toNat_eq; simp [uint.Z]
        rw [if_pos ⟨by word, by word⟩]
        rw [hb8, Hj1]
        wp_apply wp_store_slice_index $$ [Hd2] as Hd2
        · iframe; ipureintro; word
        have hj1 : j + 1 = (varint x.toNat).length := by
          have := congrArg List.length Hj4; simp at this; omega
        rw [show (sint.Z (W64 ((Pk.length + j : Nat) : Int))).toNat =
            Pk.length + ((varint x.toNat).take j).length by
          rw [List.length_take, Nat.min_eq_left (by omega)]; word]
        rw [writeAt_snoc _ _ _ _ (by rw [List.length_take, Nat.min_eq_left (by omega)]; omega),
          ← take_succ_of_drop _ _ _ _ Hj4, hj1, List.take_length, writeAt_prefix]
        wp_for_post
        iframe
        iexists (k + W64 1), _
        rw [hk1, hPs]
        rw [show W64 ((Pk.length + j : Nat) : Int) + W64 1 =
            W64 (((Pk ++ varint x.toNat).length : Nat) : Int) by
          rw [List.length_append, ← hj1]; word]
        simp only [List.length_append, List.append_assoc]
        iframe
        ipureintro; exact hkfin
    · -- the loop's end: copy, length, tag
      obtain ⟨Hk1, Hk2⟩ := Hk
      rw [show sint.nat k = o.cliSeqs.length by word, List.take_length]
      obtain ⟨P, hP⟩ : ∃ P, packedPay o.cliSeqs = P := ⟨_, rfl⟩
      rw [hP] at hEP hPL ⊢
      have hEn : (encPacked 0x32 o.cliSeqs).length ≤ sint.nat iv := by
        have := Hiv.2; omega
      have hvl := varint_length_le P.length 5 (by omega) (by omega)
      have hPZ : P.length ≤ Z.length := by omega
      ihave %Hwf := ownSlice_wf _ _ _ $$ Hsl
      ihave %Hwf2 := ownSlice_wf _ _ _ $$ Hd2
      ihave %Hd2l' := ownSlice_len _ _ _ $$ Hd2
      have hd2' : sint.nat d2.len = Z.length := by
        have := Hd2l'.1; rw [List.length_append, List.length_drop] at this; omega
      have hiv1 : sint.nat (iv - W64 (P.length : Nat)) = sint.nat iv - P.length := by word
      have Hb : 0 ≤ sint.Z (iv - W64 (P.length : Nat)) ∧
          sint.Z (iv - W64 (P.length : Nat)) ≤ sint.Z sl.len ∧ sint.Z sl.len ≤ sint.Z sl.len :=
        ⟨by word, by word, Int.le_refl _⟩
      rw [if_pos ⟨Hb.1, Hb.2.1, by word⟩]
      icases (ownSlice_slice _ _ sl (DFrac.own 1) _ Hb).1 $$ Hsl with ⟨Hs1, Hs2, Hs3⟩
      have hLn : sint.nat sl.len = bs.length := by word
      have hsub := subslice_prefix bs E (sint.nat iv) (sint.nat iv - P.length) (sint.nat sl.len)
        (by omega) (by omega) (by omega)
      have hsubl : ((bs.take (sint.nat iv)).drop (sint.nat iv - P.length)).length = P.length := by
        simp; omega
      rw [hiv1, hsub, take_prefix _ _ _ _ (by omega) (by omega),
        drop_prefix _ _ _ _ (by omega) (by omega)]
      generalize hX : (bs.take (sint.nat iv)).drop (sint.nat iv - P.length) = X at hsubl
      wp_auto
      have Hb2 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z (W64 (P.length : Nat)) ∧
          sint.Z (W64 (P.length : Nat)) ≤ sint.Z d2.len := ⟨by decide, by word, by word⟩
      rw [if_pos ⟨Hb2.1, Hb2.2.1, by word⟩]
      icases (ownSlice_slice _ _ d2 (DFrac.own 1) _ Hb2).1 $$ Hd2 with ⟨Ht1, Ht2, Ht3⟩
      have hsrc : subslice (sint.nat (W64 0)) (sint.nat (W64 (P.length : Nat))) (P ++ Z.drop P.length) = P := by
        rw [show sint.nat (W64 0) = 0 from rfl, show sint.nat (W64 (P.length : Nat)) = P.length by word]
        simp [subslice]
      rw [hsrc]
      wp_auto
      wp_apply wp_slice_copy $$ [Hs2 Ht2] as %ncp ⟨%Hncp, Hs2, -⟩
      · iframe
      have hce : P.take (X ++ E).length ++ (X ++ E).drop P.length = P ++ E := by
        rw [List.take_of_length_le (by simp; omega), List.drop_append_of_le_length (by omega),
          List.drop_of_length_le (by omega), List.nil_append]
      rw [hce]
      ihave Hsl := (ownSlice_slice _ _ sl (DFrac.own 1)
        (bs.take (sint.nat iv - P.length) ++ (P ++ E)) Hb).2 $$ [Hs1 Hs2 Hs3]
      · rw [hiv1, take_prefix _ _ _ _ (Nat.le_refl _) (by omega),
          subslice_prefix _ _ _ _ _ (Nat.le_refl _) (by omega) (by simp; omega),
          drop_prefix _ _ _ _ (by omega) (by simp; omega)]
        simp only [List.drop_take, Nat.sub_self, List.take_zero, List.nil_append]
        iframe
      have hWc : (W64 (P.length : Nat)).toNat = P.length := by word
      wp_auto
      wp_apply (wp_encodeVarintMessage sl (bs.take (sint.nat iv - P.length) ++ (P ++ E))
        (iv - W64 (P.length : Nat)) (W64 (P.length : Nat))
        (by word) (by rw [hWc, hiv1]; omega)
        (by rw [hiv1]; simp only [List.length_append, List.length_take]; omega)) $$ [Hsl] as Hsl
      · iexact Hsl
      rw [hWc, hiv1, prepend_writeAt _ _ _ _ (by omega) (by omega)]
      have hiv2 : sint.nat (iv - W64 (P.length : Nat) - W64 ((varint P.length).length : Nat) - W64 1) =
          sint.nat iv - P.length - (varint P.length).length - 1 := by word
      rw [if_pos ⟨by word, by word⟩]
      wp_apply wp_store_slice_index $$ [Hsl] as Hsl
      · iframe; ipureintro; simp only [List.length_append, List.length_take]; word
      rw [show (sint.Z (iv - W64 (P.length : Nat) - W64 ((varint P.length).length : Nat) - W64 1)).toNat
          = sint.nat iv - P.length - (varint P.length).length - 1 by word,
        prepend_set _ _ _ _ (by omega) (by omega)]
      have hEPd : encPacked 0x32 o.cliSeqs = 0x32 :: (varint P.length ++ P) := by
        simp only [packedPay] at hP
        unfold encPacked encBytes; rw [if_neg hne, hP]; simp
      wp_join_done
      iexists _
      rw [hEPd]
      rw [show (W8 50 : w8) = (0x32 : w8) from rfl]
      simp only [List.cons_append, List.append_assoc]
      rw [hiv2]
      iframe
      ipureintro
      refine ⟨by word, ?_⟩
      have := Hiv.2
      simp only [List.length_append, List.length_cons]
      omega
    done
    done
  · have hnil : o.cliSeqs = [] := List.eq_nil_of_length_eq_zero (by word)
    iexists iv
    rw [hnil, show encPacked 0x32 ([] : List w32) = [] from rfl, List.nil_append]
    iframe
    ipureintro; exact Hiv
  iNamed i; iNamed Hsl; iNamed CliSeqs; iNamed m; iNamed dAtA
  obtain ⟨E2, hE2⟩ : ∃ E2, encPacked 0x32 o.cliSeqs ++ E = E2 := ⟨_, rfl⟩
  have hE2l : E2.length = (encPacked 0x32 o.cliSeqs).length + E.length := by rw [← hE2, List.length_append]
  rw [hE2] at Hiv ⊢
  ihave %HcliIdsl := ownSlice_len _ _ _ $$ HcliIds
  wp_join iprop(∃ (iv : w64), "i" ∷ i_ptr ↦ iv ∗
      "Hsl" ∷ sl ↦* (bs.take (sint.nat iv) ++ (encPacked 0x2a o.cliIds ++ E2)) ∗
      "%Hiv" ∷ ⌜0 ≤ sint.Z iv ∧ sint.nat iv + (encPacked 0x2a o.cliIds ++ E2).length = bs.length⌝ ∗
      "CliIds" ∷ l.[ConsensusObj, go!"CliIds"] ↦{dq} v.CliIds' ∗ "m" ∷ m_ptr ↦ l ∗
      "dAtA" ∷ dAtA_ptr ↦ sl) with [i Hsl CliIds m dAtA] as ⟨%iv, i, Hsl, %Hiv, CliIds, m, dAtA⟩
  · have hne : o.cliIds ≠ [] := by
      intro h; rw [h] at HcliIdsl; simp at HcliIdsl; word
    have hPL := packedPay_length o.cliIds
    have hEP := encPacked_length 0x2a o.cliIds
    rw [if_neg hne] at hEP
    have hlenS : sint.nat v.CliIds'.len = o.cliIds.length := by word
    have hnsl : o.cliIds.length < 2 ^ 32 := by omega
    have hlenZ : sint.Z v.CliIds'.len < 2 ^ 32 := by word
    have h10 : sint.nat (v.CliIds'.len * W64 10) = 10 * o.cliIds.length := by word
    irename i => Hii
    wp_apply (wp_slice_make2 (V := w8) (v.CliIds'.len * W64 10)) as %d2 ⟨Hd2, -⟩
    · ipureintro; word
    rw [h10]
    rename_i ip
    obtain ⟨Z, hZ⟩ : ∃ Z, List.replicate (10 * o.cliIds.length) (Perennial.zero_val w8) = Z := ⟨_, rfl⟩
    have hZl : Z.length = 10 * o.cliIds.length := by rw [← hZ, List.length_replicate]
    rw [hZ, show (Perennial.zero_val w64) = W64 ((0 : Nat) : Int) from rfl]
    ihave HI : (∃ (k : w64) (nv : w32), "i" ∷ i_ptr ↦ k ∗
        "j3" ∷ j3_ptr ↦ W64 ((packedPay (o.cliIds.take (sint.nat k))).length : Nat) ∗
        "num" ∷ num_ptr ↦ nv ∗
        "Hd2" ∷ d2 ↦* (packedPay (o.cliIds.take (sint.nat k)) ++
          Z.drop (packedPay (o.cliIds.take (sint.nat k))).length) ∗
        "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.nat k ≤ o.cliIds.length⌝ : IProp GF) $$ [i j3 num Hd2]
    · iexists (W64 0), _
      simp only [show sint.nat (W64 0) = 0 from rfl, List.take_zero, packedPay, List.flatMap_nil,
        List.length_nil, List.drop_zero, List.nil_append]
      iframe
      ipureintro; exact ⟨by decide, by omega⟩
    wp_for HI
    wp_if_destruct
    · obtain ⟨Hk1, Hk2⟩ := Hk
      have hklt : sint.nat k < o.cliIds.length := by word
      have hk1 : sint.nat (k + W64 1) = sint.nat k + 1 := by word
      have hkfin : 0 ≤ sint.Z (k + W64 1) ∧ sint.nat k + 1 ≤ o.cliIds.length := ⟨by word, by word⟩
      list_elem o.cliIds (sint.nat k) as x
      have hxk : o.cliIds[sint.nat k] = x := by
        rw [List.getElem?_eq_some_iff] at Hx_lookup; exact Hx_lookup.2
      have hPs := packedPay_take_succ o.cliIds (sint.nat k) hklt
      rw [hxk] at hPs
      clear hxk
      have hPsl := packedPay_length (o.cliIds.take (sint.nat k + 1))
      rw [hPs] at hPsl
      simp only [List.length_append, List.length_take, Nat.min_eq_left hklt] at hPsl
      rw [if_pos ⟨Hk1, by word⟩]
      wp_apply wp_load_slice_index _ (sint.Z k) o.cliIds DFrac.discard x Hk1 $$ [] as -
      · isplitl []; · iexact HcliIds
        ipureintro; rw [show (sint.Z k).toNat = sint.nat k by word]; exact Hx_lookup
      ihave %Hd2l := ownSlice_len _ _ _ $$ Hd2
      obtain ⟨Pk, hPk⟩ : ∃ Pk, packedPay (o.cliIds.take (sint.nat k)) = Pk := ⟨_, rfl⟩
      rw [hPk] at hPs hPsl Hd2l ⊢
      have hPkZ : Pk.length + (varint x.toNat).length ≤ Z.length := by omega
      have hd2len : (Pk ++ Z.drop Pk.length).length = Z.length := by simp; omega
      have hd2 : sint.nat d2.len = Z.length := by rw [← Hd2l.1, hd2len]
      ihave HJ : (∃ (j : Nat) (vv : w32), "num" ∷ num_ptr ↦ vv ∗
          "j3" ∷ j3_ptr ↦ W64 ((Pk.length + j : Nat) : Int) ∗
          "Hd2" ∷ d2 ↦* writeAt (Pk ++ Z.drop Pk.length) Pk.length ((varint x.toNat).take j) ∗
          "%Hj" ∷ ⌜vv.toNat = x.toNat / 2 ^ (7 * j) ∧
            (varint x.toNat).drop j = varint (x.toNat / 2 ^ (7 * j))⌝ : IProp GF) $$ [num j3 Hd2]
      · iexists 0, x
        simp only [Nat.add_zero, List.take_zero, writeAt_nil]
        iframe
        ipureintro; simp
      wp_for HJ
      obtain ⟨Hj3, Hj4⟩ := Hj
      have hjk : j < (varint x.toNat).length := by
        apply Nat.lt_of_not_le; intro hj
        rw [List.drop_eq_nil_of_le hj] at Hj4
        exact varint_ne_nil _ Hj4.symm
      have hwl : (writeAt (Pk ++ Z.drop Pk.length) Pk.length ((varint x.toNat).take j)).length = Z.length := by
        rw [writeAt_length _ _ _ (by simp; omega), hd2len]
      wp_if_destruct
      · have hge : ¬ x.toNat / 2 ^ (7 * j) < 128 := by rw [← Hj3]; word
        rw [varint_ge _ hge] at Hj4
        rw [if_pos ⟨by word, by word⟩]
        rw [byte_cont, show (W64 (uint.Z vv)).toNat = vv.toNat by simp [uint.Z]; have := vv.isLt; omega, Hj3]
        wp_apply wp_store_slice_index $$ [Hd2] as Hd2
        · iframe; ipureintro; word
        wp_for_post
        iframe
        iexists j + 1, _
        rw [show (sint.Z (W64 ((Pk.length + j : Nat) : Int))).toNat =
            Pk.length + ((varint x.toNat).take j).length by
          rw [List.length_take, Nat.min_eq_left (by omega)]; word]
        rw [writeAt_snoc _ _ _ _ (by rw [List.length_take, Nat.min_eq_left (by omega)]; omega),
          ← take_succ_of_drop _ _ _ _ Hj4]
        rw [show W64 ((Pk.length + j : Nat) : Int) + W64 1 = W64 ((Pk.length + (j + 1) : Nat) : Int) by
          word]
        iframe
        ipureintro
        refine ⟨?_, ?_⟩
        · rw [div_pow_succ]
          have : (vv >>> W64 7).toNat = vv.toNat / 128 := by
            rw [BitVec.ushiftRight_eq', BitVec.toNat_ushiftRight, show (W64 7).toNat = 7 from rfl,
              Nat.shiftRight_eq_div_pow]
          rw [this, Hj3]
        · rw [div_pow_succ, ← List.drop_drop, Hj4]; rfl
      · have hlt : x.toNat / 2 ^ (7 * j) < 128 := by rw [← Hj3]; word
        rw [varint_lt _ hlt] at Hj4
        have hb8 : W8 (uint.Z vv) = BitVec.ofNat 8 vv.toNat := by
          apply BitVec.eq_of_toNat_eq; simp [uint.Z]
        rw [if_pos ⟨by word, by word⟩]
        rw [hb8, Hj3]
        wp_apply wp_store_slice_index $$ [Hd2] as Hd2
        · iframe; ipureintro; word
        have hj3 : j + 1 = (varint x.toNat).length := by
          have := congrArg List.length Hj4; simp at this; omega
        rw [show (sint.Z (W64 ((Pk.length + j : Nat) : Int))).toNat =
            Pk.length + ((varint x.toNat).take j).length by
          rw [List.length_take, Nat.min_eq_left (by omega)]; word]
        rw [writeAt_snoc _ _ _ _ (by rw [List.length_take, Nat.min_eq_left (by omega)]; omega),
          ← take_succ_of_drop _ _ _ _ Hj4, hj3, List.take_length, writeAt_prefix]
        wp_for_post
        iframe
        iexists (k + W64 1), _
        rw [hk1, hPs]
        rw [show W64 ((Pk.length + j : Nat) : Int) + W64 1 =
            W64 (((Pk ++ varint x.toNat).length : Nat) : Int) by
          rw [List.length_append, ← hj3]; word]
        simp only [List.length_append, List.append_assoc]
        iframe
        ipureintro; exact hkfin
    · -- the loop's end: copy, length, tag
      obtain ⟨Hk1, Hk2⟩ := Hk
      rw [show sint.nat k = o.cliIds.length by word, List.take_length]
      obtain ⟨P, hP⟩ : ∃ P, packedPay o.cliIds = P := ⟨_, rfl⟩
      rw [hP] at hEP hPL ⊢
      have hEn : (encPacked 0x2a o.cliIds).length ≤ sint.nat iv := by
        have := Hiv.2; omega
      have hvl := varint_length_le P.length 5 (by omega) (by omega)
      have hPZ : P.length ≤ Z.length := by omega
      ihave %Hwf := ownSlice_wf _ _ _ $$ Hsl
      ihave %Hwf2 := ownSlice_wf _ _ _ $$ Hd2
      ihave %Hd2l' := ownSlice_len _ _ _ $$ Hd2
      have hd2' : sint.nat d2.len = Z.length := by
        have := Hd2l'.1; rw [List.length_append, List.length_drop] at this; omega
      have hiv1 : sint.nat (iv - W64 (P.length : Nat)) = sint.nat iv - P.length := by word
      have Hb : 0 ≤ sint.Z (iv - W64 (P.length : Nat)) ∧
          sint.Z (iv - W64 (P.length : Nat)) ≤ sint.Z sl.len ∧ sint.Z sl.len ≤ sint.Z sl.len :=
        ⟨by word, by word, Int.le_refl _⟩
      rw [if_pos ⟨Hb.1, Hb.2.1, by word⟩]
      icases (ownSlice_slice _ _ sl (DFrac.own 1) _ Hb).1 $$ Hsl with ⟨Hs1, Hs2, Hs3⟩
      have hLn : sint.nat sl.len = bs.length := by word
      have hsub := subslice_prefix bs E2 (sint.nat iv) (sint.nat iv - P.length) (sint.nat sl.len)
        (by omega) (by omega) (by omega)
      have hsubl : ((bs.take (sint.nat iv)).drop (sint.nat iv - P.length)).length = P.length := by
        simp; omega
      rw [hiv1, hsub, take_prefix _ _ _ _ (by omega) (by omega),
        drop_prefix _ _ _ _ (by omega) (by omega)]
      generalize hX : (bs.take (sint.nat iv)).drop (sint.nat iv - P.length) = X at hsubl
      wp_auto
      have Hb2 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z (W64 (P.length : Nat)) ∧
          sint.Z (W64 (P.length : Nat)) ≤ sint.Z d2.len := ⟨by decide, by word, by word⟩
      rw [if_pos ⟨Hb2.1, Hb2.2.1, by word⟩]
      icases (ownSlice_slice _ _ d2 (DFrac.own 1) _ Hb2).1 $$ Hd2 with ⟨Ht1, Ht2, Ht3⟩
      have hsrc : subslice (sint.nat (W64 0)) (sint.nat (W64 (P.length : Nat))) (P ++ Z.drop P.length) = P := by
        rw [show sint.nat (W64 0) = 0 from rfl, show sint.nat (W64 (P.length : Nat)) = P.length by word]
        simp [subslice]
      rw [hsrc]
      wp_auto
      wp_apply wp_slice_copy $$ [Hs2 Ht2] as %ncp ⟨%Hncp, Hs2, -⟩
      · iframe
      have hce : P.take (X ++ E2).length ++ (X ++ E2).drop P.length = P ++ E2 := by
        rw [List.take_of_length_le (by simp; omega), List.drop_append_of_le_length (by omega),
          List.drop_of_length_le (by omega), List.nil_append]
      rw [hce]
      ihave Hsl := (ownSlice_slice _ _ sl (DFrac.own 1)
        (bs.take (sint.nat iv - P.length) ++ (P ++ E2)) Hb).2 $$ [Hs1 Hs2 Hs3]
      · rw [hiv1, take_prefix _ _ _ _ (Nat.le_refl _) (by omega),
          subslice_prefix _ _ _ _ _ (Nat.le_refl _) (by omega) (by simp; omega),
          drop_prefix _ _ _ _ (by omega) (by simp; omega)]
        simp only [List.drop_take, Nat.sub_self, List.take_zero, List.nil_append]
        iframe
      have hWc : (W64 (P.length : Nat)).toNat = P.length := by word
      wp_auto
      wp_apply (wp_encodeVarintMessage sl (bs.take (sint.nat iv - P.length) ++ (P ++ E2))
        (iv - W64 (P.length : Nat)) (W64 (P.length : Nat))
        (by word) (by rw [hWc, hiv1]; omega)
        (by rw [hiv1]; simp only [List.length_append, List.length_take]; omega)) $$ [Hsl] as Hsl
      · iexact Hsl
      rw [hWc, hiv1, prepend_writeAt _ _ _ _ (by omega) (by omega)]
      have hiv2 : sint.nat (iv - W64 (P.length : Nat) - W64 ((varint P.length).length : Nat) - W64 1) =
          sint.nat iv - P.length - (varint P.length).length - 1 := by word
      rw [if_pos ⟨by word, by word⟩]
      wp_apply wp_store_slice_index $$ [Hsl] as Hsl
      · iframe; ipureintro; simp only [List.length_append, List.length_take]; word
      rw [show (sint.Z (iv - W64 (P.length : Nat) - W64 ((varint P.length).length : Nat) - W64 1)).toNat
          = sint.nat iv - P.length - (varint P.length).length - 1 by word,
        prepend_set _ _ _ _ (by omega) (by omega)]
      have hEPd : encPacked 0x2a o.cliIds = 0x2a :: (varint P.length ++ P) := by
        simp only [packedPay] at hP
        unfold encPacked encBytes; rw [if_neg hne, hP]; simp
      wp_join_done
      iexists _
      rw [hEPd]
      rw [show (W8 42 : w8) = (0x2a : w8) from rfl]
      simp only [List.cons_append, List.append_assoc]
      rw [hiv2]
      iframe
      ipureintro
      refine ⟨by word, ?_⟩
      have := Hiv.2
      simp only [List.length_append, List.length_cons]
      omega
    done
    done
  · have hnil : o.cliIds = [] := List.eq_nil_of_length_eq_zero (by word)
    iexists iv
    rw [hnil, show encPacked 0x2a ([] : List w32) = [] from rfl, List.nil_append]
    iframe
    ipureintro; exact Hiv
  iNamed i; iNamed Hsl; iNamed CliIds; iNamed m; iNamed dAtA
  obtain ⟨E3, hE3⟩ : ∃ E3, encPacked 0x2a o.cliIds ++ E2 = E3 := ⟨_, rfl⟩
  have hE3l : E3.length = (encPacked 0x2a o.cliIds).length + E2.length := by rw [← hE3, List.length_append]
  rw [hE3] at Hiv ⊢
  wp_join iprop(∃ (iv : w64), "i" ∷ i_ptr ↦ iv ∗
      "Hsl" ∷ sl ↦* (bs.take (sint.nat iv) ++ ((if o.isNull then [(0x20 : w8), 1] else []) ++ E3)) ∗
      "%Hiv" ∷ ⌜0 ≤ sint.Z iv ∧ sint.nat iv + ((if o.isNull then [(0x20 : w8), 1] else []) ++ E3).length = bs.length⌝ ∗
      "IsNull" ∷ l.[ConsensusObj, go!"IsNull"] ↦{dq} v.IsNull' ∗ "m" ∷ m_ptr ↦ l ∗
      "dAtA" ∷ dAtA_ptr ↦ sl) at next with [i Hsl IsNull m dAtA] as ⟨%iv, i, Hsl, %Hiv, IsNull, m, dAtA⟩
  · rw [hp4]
    cases hnull : o.isNull
    · wp_auto
      wp_join_done
      iexists iv
      simp only [Bool.false_eq_true, ite_false, List.nil_append]
      iframe
      ipureintro; exact Hiv
    · wp_auto
      have hS' := hS
      simp only [hnull, ite_true] at hS'
      have hge2 : 2 ≤ sint.nat iv := by have := Hiv.2; omega
      ihave %Hl2 := ownSlice_len _ _ _ $$ Hsl
      rw [if_pos ⟨by word, by word⟩]
      wp_apply wp_store_slice_index $$ [Hsl] as Hsl
      · iframe; ipureintro; simp only [List.length_append, List.length_take]; word
      rw [show (sint.Z (iv - W64 1)).toNat = sint.nat iv - 1 by word,
        prepend_set _ _ _ _ (by omega) (by omega)]
      rw [if_pos ⟨by word, by word⟩]
      wp_apply wp_store_slice_index $$ [Hsl] as Hsl
      · iframe; ipureintro; simp only [List.length_append, List.length_take]; word
      rw [show (sint.Z (iv - W64 1 - W64 1)).toNat = sint.nat iv - 1 - 1 by word,
        prepend_set _ _ _ _ (by omega) (by omega)]
      wp_join_done
      iexists _
      simp only [ite_true, List.cons_append, List.nil_append]
      rw [show (W8 32 : w8) = (0x20 : w8) from rfl, show (W8 1 : w8) = (1 : w8) from rfl,
        show sint.nat (iv - W64 1 - W64 1) = sint.nat iv - 1 - 1 by word]
      iframe
      ipureintro
      refine ⟨by word, ?_⟩
      have := Hiv.2
      simp only [List.length_cons]
      omega
  iNamed i; iNamed Hsl; iNamed IsNull; iNamed m; iNamed dAtA
  obtain ⟨E4, hE4⟩ : ∃ E4, (if o.isNull then [(0x20 : w8), 1] else []) ++ E3 = E4 := ⟨_, rfl⟩
  have hisn : (if o.isNull then [(0x20 : w8), 1] else []).length = if o.isNull then 2 else 0 := by
    split <;> rfl
  have hE4l : E4.length = (if o.isNull then [(0x20 : w8), 1] else []).length + E3.length := by
    rw [← hE4, List.length_append]
  rw [hE4] at Hiv ⊢
  wp_join iprop(∃ (iv : w64), "i" ∷ i_ptr ↦ iv ∗
      "Hsl" ∷ sl ↦* (bs.take (sint.nat iv) ++ (encScalar 0x18 o.svrSeq.toNat ++ E4)) ∗
      "%Hiv" ∷ ⌜0 ≤ sint.Z iv ∧ sint.nat iv + (encScalar 0x18 o.svrSeq.toNat ++ E4).length = bs.length⌝ ∗
      "SvrSeq" ∷ l.[ConsensusObj, go!"SvrSeq"] ↦{dq} v.SvrSeq' ∗ "m" ∷ m_ptr ↦ l ∗
      "dAtA" ∷ dAtA_ptr ↦ sl) with [i Hsl SvrSeq m dAtA] as ⟨%iv, i, Hsl, %Hiv, SvrSeq, m, dAtA⟩
  · -- zero: nothing written
    rw [hp3] at Hif
    have hx : o.svrSeq.toNat = 0 := by rw [Hif]; rfl
    iexists iv
    rw [show encScalar 0x18 o.svrSeq.toNat = [] by rw [encScalar_eq_nil]; exact hx, List.nil_append]
    iframe
    ipureintro; exact Hiv
  · -- nonzero: varint and tag
    rw [hp3] at Hif ⊢
    have hx : o.svrSeq.toNat ≠ 0 := fun h => Hif (BitVec.eq_of_toNat_eq (by simpa using h))
    have hsc := encScalar_ne_nil (t := 0x18) (n := o.svrSeq.toNat) (by rw [Ne, encScalar_eq_nil]; exact hx)
    have hEn := hle
    rw [hcl, ← hS] at hEn
    have hvl := varint_length_le o.svrSeq.toNat 5 (by have := o.svrSeq.isLt; omega) (by omega)
    have hW' : (W64 (uint.Z o.svrSeq)).toNat = o.svrSeq.toNat := by simp [uint.Z]; have := o.svrSeq.isLt; omega
    have hlx := encScalar_length 0x18 o.svrSeq.toNat
    rw [if_neg hx] at hlx
    have hge : 1 + (varint o.svrSeq.toNat).length ≤ sint.nat iv := by
      have := Hiv.2
      try simp only [List.length_append] at this
      omega
    wp_apply (wp_encodeVarintMessage sl (bs.take (sint.nat iv) ++ (E4)) iv (W64 (uint.Z o.svrSeq))
      Hiv.1 (by rw [hW']; omega) (by simp only [List.length_append, List.length_take]; omega))
      $$ [Hsl] as Hsl
    · iexact Hsl
    rw [hW', prepend_writeAt _ _ _ _ (by omega) (by omega)]
    rw [if_pos ⟨by word, by word⟩]
    wp_apply wp_store_slice_index $$ [Hsl] as Hsl
    · iframe; ipureintro; simp only [List.length_append, List.length_take]; word
    rw [show (sint.Z (iv - W64 ((varint o.svrSeq.toNat).length : Nat) - W64 1)).toNat
        = sint.nat iv - (varint o.svrSeq.toNat).length - 1 by word,
      prepend_set _ _ _ _ (by omega) (by omega)]
    wp_join_done
    iexists _
    rw [hsc.1]
    rw [show (W8 24 : w8) = (0x18 : w8) from rfl]
    simp only [List.cons_append]
    rw [show sint.nat (iv - W64 ((varint o.svrSeq.toNat).length : Nat) - W64 1) =
      sint.nat iv - (varint o.svrSeq.toNat).length - 1 by word]
    iframe
    ipureintro
    refine ⟨by word, ?_⟩
    have := Hiv.2
    simp only [List.length_append, List.length_cons] at this ⊢
    omega
  iNamed i; iNamed Hsl; iNamed SvrSeq; iNamed m; iNamed dAtA
  wp_join iprop(∃ (iv : w64), "i" ∷ i_ptr ↦ iv ∗
      "Hsl" ∷ sl ↦* (bs.take (sint.nat iv) ++ (encScalar 0x10 o.proSeq.toNat ++ (encScalar 0x18 o.svrSeq.toNat ++ E4))) ∗
      "%Hiv" ∷ ⌜0 ≤ sint.Z iv ∧ sint.nat iv + (encScalar 0x10 o.proSeq.toNat ++ (encScalar 0x18 o.svrSeq.toNat ++ E4)).length = bs.length⌝ ∗
      "ProSeq" ∷ l.[ConsensusObj, go!"ProSeq"] ↦{dq} v.ProSeq' ∗ "m" ∷ m_ptr ↦ l ∗
      "dAtA" ∷ dAtA_ptr ↦ sl) with [i Hsl ProSeq m dAtA] as ⟨%iv, i, Hsl, %Hiv, ProSeq, m, dAtA⟩
  · -- zero: nothing written
    rw [hp2] at Hif
    have hx : o.proSeq.toNat = 0 := by rw [Hif]; rfl
    iexists iv
    rw [show encScalar 0x10 o.proSeq.toNat = [] by rw [encScalar_eq_nil]; exact hx, List.nil_append]
    iframe
    ipureintro; exact Hiv
  · -- nonzero: varint and tag
    rw [hp2] at Hif ⊢
    have hx : o.proSeq.toNat ≠ 0 := fun h => Hif (BitVec.eq_of_toNat_eq (by simpa using h))
    have hsc := encScalar_ne_nil (t := 0x10) (n := o.proSeq.toNat) (by rw [Ne, encScalar_eq_nil]; exact hx)
    have hEn := hle
    rw [hcl, ← hS] at hEn
    have hvl := varint_length_le o.proSeq.toNat 5 (by have := o.proSeq.isLt; omega) (by omega)
    have hW' : (W64 (uint.Z o.proSeq)).toNat = o.proSeq.toNat := by simp [uint.Z]; have := o.proSeq.isLt; omega
    have hlx := encScalar_length 0x10 o.proSeq.toNat
    rw [if_neg hx] at hlx
    have hge : 1 + (varint o.proSeq.toNat).length ≤ sint.nat iv := by
      have := Hiv.2
      try simp only [List.length_append] at this
      omega
    wp_apply (wp_encodeVarintMessage sl (bs.take (sint.nat iv) ++ (encScalar 0x18 o.svrSeq.toNat ++ E4)) iv (W64 (uint.Z o.proSeq))
      Hiv.1 (by rw [hW']; omega) (by simp only [List.length_append, List.length_take]; omega))
      $$ [Hsl] as Hsl
    · iexact Hsl
    rw [hW', prepend_writeAt _ _ _ _ (by omega) (by omega)]
    rw [if_pos ⟨by word, by word⟩]
    wp_apply wp_store_slice_index $$ [Hsl] as Hsl
    · iframe; ipureintro; simp only [List.length_append, List.length_take]; word
    rw [show (sint.Z (iv - W64 ((varint o.proSeq.toNat).length : Nat) - W64 1)).toNat
        = sint.nat iv - (varint o.proSeq.toNat).length - 1 by word,
      prepend_set _ _ _ _ (by omega) (by omega)]
    wp_join_done
    iexists _
    rw [hsc.1]
    rw [show (W8 16 : w8) = (0x10 : w8) from rfl]
    simp only [List.cons_append]
    rw [show sint.nat (iv - W64 ((varint o.proSeq.toNat).length : Nat) - W64 1) =
      sint.nat iv - (varint o.proSeq.toNat).length - 1 by word]
    iframe
    ipureintro
    refine ⟨by word, ?_⟩
    have := Hiv.2
    simp only [List.length_append, List.length_cons] at this ⊢
    omega
  iNamed i; iNamed Hsl; iNamed ProSeq; iNamed m; iNamed dAtA
  wp_join iprop(∃ (iv : w64), "i" ∷ i_ptr ↦ iv ∗
      "Hsl" ∷ sl ↦* (bs.take (sint.nat iv) ++ (encScalar 0x08 o.proId.toNat ++ (encScalar 0x10 o.proSeq.toNat ++ (encScalar 0x18 o.svrSeq.toNat ++ E4)))) ∗
      "%Hiv" ∷ ⌜0 ≤ sint.Z iv ∧ sint.nat iv + (encScalar 0x08 o.proId.toNat ++ (encScalar 0x10 o.proSeq.toNat ++ (encScalar 0x18 o.svrSeq.toNat ++ E4))).length = bs.length⌝ ∗
      "ProId" ∷ l.[ConsensusObj, go!"ProId"] ↦{dq} v.ProId' ∗ "m" ∷ m_ptr ↦ l ∗
      "dAtA" ∷ dAtA_ptr ↦ sl) with [i Hsl ProId m dAtA] as ⟨%iv, i, Hsl, %Hiv, ProId, m, dAtA⟩
  · -- zero: nothing written
    rw [hp1] at Hif
    have hx : o.proId.toNat = 0 := by rw [Hif]; rfl
    iexists iv
    rw [show encScalar 0x08 o.proId.toNat = [] by rw [encScalar_eq_nil]; exact hx, List.nil_append]
    iframe
    ipureintro; exact Hiv
  · -- nonzero: varint and tag
    rw [hp1] at Hif ⊢
    have hx : o.proId.toNat ≠ 0 := fun h => Hif (BitVec.eq_of_toNat_eq (by simpa using h))
    have hsc := encScalar_ne_nil (t := 0x08) (n := o.proId.toNat) (by rw [Ne, encScalar_eq_nil]; exact hx)
    have hEn := hle
    rw [hcl, ← hS] at hEn
    have hvl := varint_length_le o.proId.toNat 5 (by have := o.proId.isLt; omega) (by omega)
    have hW' : (W64 (uint.Z o.proId)).toNat = o.proId.toNat := by simp [uint.Z]; have := o.proId.isLt; omega
    have hlx := encScalar_length 0x08 o.proId.toNat
    rw [if_neg hx] at hlx
    have hge : 1 + (varint o.proId.toNat).length ≤ sint.nat iv := by
      have := Hiv.2
      try simp only [List.length_append] at this
      omega
    wp_apply (wp_encodeVarintMessage sl (bs.take (sint.nat iv) ++ (encScalar 0x10 o.proSeq.toNat ++ (encScalar 0x18 o.svrSeq.toNat ++ E4))) iv (W64 (uint.Z o.proId))
      Hiv.1 (by rw [hW']; omega) (by simp only [List.length_append, List.length_take]; omega))
      $$ [Hsl] as Hsl
    · iexact Hsl
    rw [hW', prepend_writeAt _ _ _ _ (by omega) (by omega)]
    rw [if_pos ⟨by word, by word⟩]
    wp_apply wp_store_slice_index $$ [Hsl] as Hsl
    · iframe; ipureintro; simp only [List.length_append, List.length_take]; word
    rw [show (sint.Z (iv - W64 ((varint o.proId.toNat).length : Nat) - W64 1)).toNat
        = sint.nat iv - (varint o.proId.toNat).length - 1 by word,
      prepend_set _ _ _ _ (by omega) (by omega)]
    wp_join_done
    iexists _
    rw [hsc.1]
    rw [show (W8 8 : w8) = (0x08 : w8) from rfl]
    simp only [List.cons_append]
    rw [show sint.nat (iv - W64 ((varint o.proId.toNat).length : Nat) - W64 1) =
      sint.nat iv - (varint o.proId.toNat).length - 1 by word]
    iframe
    ipureintro
    refine ⟨by word, ?_⟩
    have := Hiv.2
    simp only [List.length_append, List.length_cons] at this ⊢
    omega
  iNamed i; iNamed Hsl; iNamed ProId; iNamed m; iNamed dAtA
  have hEall : encScalar 0x08 o.proId.toNat ++ (encScalar 0x10 o.proSeq.toNat ++ (encScalar 0x18 o.svrSeq.toNat ++ E4)) = encObj o := by
    rw [← hE4, ← hE3, ← hE2, ← hE]; simp [encObj, List.append_assoc]
  rw [hEall] at Hiv ⊢
  ihave H := typedPointsto_combine l v dq Hnn $$ [ProId ProSeq SvrSeq IsNull CliIds CliSeqs Commands]
  · simp only [TypedPointsto.typedPointstoDef]; iframe
  rw [show sl.len - iv = W64 ((encObj o).length : Nat) by word,
    show bs.length - (encObj o).length = sint.nat iv by omega]
  iapply HΦ
  iframe

end proof
end Perennial.rabia.internal.message

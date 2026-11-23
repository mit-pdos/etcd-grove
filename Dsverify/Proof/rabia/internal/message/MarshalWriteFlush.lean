/-
(Ported from dsverify-lab `examples/rabia/proof/Proof/rabia/internal/message/MarshalWriteFlush.lean`, run
`rabia-r1wake-1`, onto the revised bufio.)

`(*Command).MarshalWriteFlush`'s and `(*Msg).MarshalWriteFlush`'s proofs: `Marshal` (C1's
`Marshal.spec`, under the premise's bound), `BufWrite` (its error ignored: it sticks in
the writer), `Flush` (returns the sticky error, else sends the rest).
`Command`'s first runs G12's loop (a string longer than `0xffffffff`: `Flush`, return; with at
most one string the encoding is then `< 2^33`, `encCmd_lt33`), and an encoding of `2^32` bytes
or more goes through `hBWL` (N8: nothing written), which needs the global
`errFrameTooLong` (`errFrameTooLong_get`, from the package fact `msgFact`).
Rest on C1's proofs of the `Marshal` specs (`wp_of` takes them).
-/
module

public import Dsverify.Proof.rabia.internal.message.SpecInternal
public import Dsverify.Proof.rabia.internal.message.Command__Marshal
public import Dsverify.Proof.rabia.internal.message.Msg__Marshal
public import Spec.bufio.Writer__Flush
public import Dsverify.Proof.rabia.internal.message.Internal

@[expose] public section

noncomputable section

namespace Perennial.rabia.internal.message

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode model

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [package_sem : rabia.internal.message.Assumptions]
variable [_root_.Perennial.bufio.Assumptions]

omit go_gctx in
/-- With at most one command string, of at most `0xffffffff` bytes (G12's loop passed), the
encoding is shorter than `2 ^ 33` (`Command.Marshal.spec`'s premise). -/
theorem encCmd_lt33 (c : CmdV) (h1 : c.commands.length ≤ 1)
    (h2 : ∀ s ∈ c.commands, s.length ≤ 4294967295) : (encCmd c).length < 2 ^ 33 := by
  rcases c with ⟨i1, i2, i3, cmds⟩
  have hlt : ∀ x : w32, (varint x.toNat).length ≤ 5 := fun x =>
    varint_length_le _ _ (by have := x.isLt; omega) (by omega)
  have hif : ∀ x : w32, (if x.toNat = 0 then 0 else 1 + (varint x.toNat).length) ≤ 6 := by
    intro x; have := hlt x; split <;> omega
  have a := hif i1; have b := hif i2; have d := hif i3
  rw [encCmd_length]
  simp only [encScalar_length] at h1 h2 ⊢
  rcases cmds with _ | ⟨s, _ | ⟨s', t⟩⟩
  · simp only [List.flatMap_nil, List.length_nil]; omega
  · have hs := h2 s (by simp)
    have := varint_length_le s.length 5 (by omega) (by omega)
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, encBytes_length]
    omega
  · simp at h1

omit go_gctx in
/-- A command string is no longer than the encoding. -/
theorem encCmd_ge (c : CmdV) (s : GoString) (hs : s ∈ c.commands) : s.length ≤ (encCmd c).length := by
  rw [encCmd_length]
  have : (encBytes 0x22 s).length ≤ (c.commands.flatMap (encBytes 0x22)).length := by
    obtain ⟨l1, l2, h⟩ := List.append_of_mem hs
    rw [h]
    simp only [List.flatMap_append, List.flatMap_cons, List.length_append]; omega
  rw [encBytes_length] at this; omega

set_option maxHeartbeats 2000000 in
/-- `Command.MarshalWriteFlush.spec`, given `Marshal`'s spec (the global `errFrameTooLong`
from the package fact, `errFrameTooLong_get`). -/
theorem Command.MarshalWriteFlush.wp_proof
    (hM : Command.Marshal.spec (GF := GF))
    (hBW : BufWrite.spec (GF := GF)) (hBWL : BufWrite.specTooLong (GF := GF))
    (wp_Flush : EtcdGrove.bufio.Writer.Flush.spec (GF := GF) (hG := hG)) :
    ∀ (l : Loc) (v : Command) (c : CmdV) (bw : Loc) (wi : GoInterfaceOk)
      (J Q : List w8 → IProp GF) (Ew : GoInterface → IProp GF) (sz : Nat) (sent pend : List w8)
      (err : GoInterface),
    {{ isPkgInit (PROP := IProp GF) pkg_id.rabia.internal.message ∗
        l ↦□ v ∗ cmdRep v c ∗
        ⌜c.commands.length ≤ 1⌝ ∗ EtcdGrove.io.streamWriterOk wi J Q Ew ∗
        EtcdGrove.bufio.ownBufWriter bw wi J Q Ew sz sent pend err ∗
        □ (⌜(encCmd c).length < 2 ^ 32⌝ -∗ Q (sent ++ pend ++ frame (encCmd c))) }}
      (App (Val (l @!! go.GoType.PointerType Command.ty @!! go!"MarshalWriteFlush")) (Val #bw))
    {{ (e : GoInterface), RET #e; ∃ (sent' pend' : List w8),
        ⌜sent <+: sent' ∧
          ((encCmd c).length < 2 ^ 32 ∧ sent' ++ pend' <+: sent ++ pend ++ frame (encCmd c) ∧
            (e = interface.nil → sent' = sent ++ pend ++ frame (encCmd c) ∧ pend' = []) ∨
           2 ^ 32 ≤ (encCmd c).length ∧ sent' ++ pend' <+: sent ++ pend)⌝ ∗
        EtcdGrove.bufio.ownBufWriter bw wi J Q Ew sz sent' pend' e }} := by
  intro l v c bw wi J Q Ew sz sent pend err
  wp_start as ⟨#Hl, #Hrep, %Hc1, #Hwr, Hown, #HQ⟩
  ihave ⟨#Hpb, #Hpio, #Hpbin⟩ := msgPkgDeps_get $$ Hpkg
  ihave #Hrep' := Hrep
  iunfold cmdRep at Hrep'
  icases Hrep' with ⟨%Hp, #Hcmds⟩
  ihave #Hl' := Hl
  icases typedPointsto_split _ _ _ $$ Hl' with Hl'
  simp only [TypedPointsto.typedPointstoDef]
  icases Hl' with ⟨-, -, -, #HCommands, -⟩
  wp_auto
  ihave %Hcl := ownSlice_len _ _ _ $$ Hcmds
  ihave HI : (∃ (i : w64) (sv : GoString), "i" ∷ i_ptr ↦ i ∗ "s" ∷ s_ptr ↦ sv ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.nat i ≤ c.commands.length ∧
        ∀ j < sint.nat i, ∀ s, c.commands[j]? = some s → s.length ≤ 4294967295⌝ : IProp GF) $$ [i s]
  · iexists _, _
    iframe
    ipureintro
    refine ⟨by decide, by simp, fun j hj => ?_⟩
    exfalso; have : sint.nat (W64 0) = 0 := rfl; omega
  wp_for HI
  wp_if_destruct
  · obtain ⟨Hi1, Hi2, Hi3⟩ := Hi
    have hlt' : sint.Z i < sint.Z v.Commands'.len := by simpa using Hif
    have hilt : sint.nat i < c.commands.length := by
      have h1 : ((sint.nat i : Nat) : Int) = sint.Z i := Int.toNat_of_nonneg Hi1
      have h2 : ((sint.nat v.Commands'.len : Nat) : Int) = sint.Z v.Commands'.len :=
        Int.toNat_of_nonneg Hcl.2
      omega
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨Hi1, hlt'⟩)]
    list_elem c.commands (sint.nat i) as cmd
    wp_apply wp_load_slice_index _ (sint.Z i) c.commands DFrac.discard cmd Hi1 $$ [] as -
    · isplitl []; · iexact Hcmds
      ipureintro; rw [show (sint.Z i).toNat = sint.nat i by word]; exact Hcmd_lookup
    wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %Hslen
    have hW : uint.Z (W64 (cmd.length : Int)) = cmd.length := by word
    wp_if_destruct
    · -- G12: a command string too long for a frame: flush, return
      have hlong : 4294967295 < cmd.length := by
        have h2 : uint.Z (W64 4294967295) = 4294967295 := rfl
        omega
      wp_apply wp_Flush bw wi J Q Ew sz sent pend _ $$ [$Hown] as %e2 ⟨%k2, %Hk2, Hown⟩
      wp_for_post
      iapply HΦ
      iexists sent ++ pend.take k2, pend.drop k2
      iframe Hown
      ipureintro
      refine ⟨List.prefix_append _ _, Or.inr ⟨?_, ?_⟩⟩
      · have := encCmd_ge c cmd (List.mem_of_getElem? Hcmd_lookup); omega
      · rw [List.append_assoc, List.take_append_drop]; exact List.prefix_refl _
    · -- this string fits
      wp_for_post
      iframe
      iexists _, _
      iframe
      have hs1 : sint.nat (i + W64 1) = sint.nat i + 1 := by word
      ipureintro
      refine ⟨by word, by omega, fun j hj s hs => ?_⟩
      rw [hs1] at hj
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
      · exact Hi3 j hj s hs
      · rw [Hcmd_lookup] at hs; cases hs
        have h2 : uint.Z (W64 4294967295) = 4294967295 := rfl
        omega
  -- the loop's end: every command string fits
  obtain ⟨Hi1, Hi2, Hi3⟩ := Hi
  have hiend : sint.nat i = c.commands.length := by
    have hge : ¬ sint.Z i < sint.Z v.Commands'.len := by simpa using Hif
    have h1 : ((sint.nat i : Nat) : Int) = sint.Z i := Int.toNat_of_nonneg Hi1
    have h2 : ((sint.nat v.Commands'.len : Nat) : Int) = sint.Z v.Commands'.len :=
      Int.toNat_of_nonneg Hcl.2
    omega
  have hall : ∀ s ∈ c.commands, s.length ≤ 4294967295 := by
    intro s hs
    obtain ⟨j, hj, hjs⟩ := List.getElem_of_mem hs
    exact Hi3 j (by omega) s (by rw [List.getElem?_eq_getElem hj, hjs])
  have Hb33 := encCmd_lt33 c Hc1 hall
  wp_apply hM l v c _ $$ [$Hl $Hrep] as %dsl ⟨-, Hd⟩
  · ipureintro; exact Hb33
  by_cases h32 : (encCmd c).length < 2 ^ 32
  · -- the frame is written
    ihave #HQ' := HQ $$ %h32
    wp_apply hBW bw wi J Q Ew sz sent pend err dsl _ _ $$ [$Hpkg $Hwr $Hown $HQ' $Hd]
      as %e1 ⟨%k, %sent1, %pend1, %Hk, -, Hown⟩
    · ipureintro; exact h32
    obtain ⟨hkl, hks, hkp, hke⟩ := Hk
    wp_apply wp_Flush bw wi J Q Ew sz sent1 pend1 _ $$ [$Hown] as %e2 ⟨%k2, %Hk2, Hown⟩
    obtain ⟨hk2l, hk2e, hk2s⟩ := Hk2
    iapply HΦ
    iexists sent1 ++ pend1.take k2, pend1.drop k2
    iframe Hown
    ipureintro
    refine ⟨hkp.trans (List.prefix_append _ _), Or.inl ⟨h32, ?_, fun h => ?_⟩⟩
    · rw [List.append_assoc, List.take_append_drop, hks]
      exact (List.prefix_append_right_inj _).2 (List.take_prefix _ _)
    · have he1 : e1 = interface.nil := by
        by_cases hne : e1 = interface.nil
        · exact hne
        · rw [(hk2s hne).1] at h; exact absurd h hne
      rw [hk2e h, List.take_length, List.drop_length, hks, hke he1, List.take_length]
      exact ⟨rfl, rfl⟩
  · -- N8: an encoding too long for a frame: `BufWrite` writes nothing
    wp_apply hBWL bw dsl _ _ (by omega) $$ [$Hpkg $Hd] as %e1 ⟨%He1, -⟩
    wp_apply wp_Flush bw wi J Q Ew sz sent pend _ $$ [$Hown] as %e2 ⟨%k2, %Hk2, Hown⟩
    iapply HΦ
    iexists sent ++ pend.take k2, pend.drop k2
    iframe Hown
    ipureintro
    refine ⟨List.prefix_append _ _, Or.inr ⟨by omega, ?_⟩⟩
    rw [List.append_assoc, List.take_append_drop]; exact List.prefix_refl _

set_option maxHeartbeats 1000000 in
theorem Msg.MarshalWriteFlush.wp_proof
    (hM : Msg.Marshal.spec (GF := GF))
    (hBW : BufWrite.spec (GF := GF)) (hBWL : BufWrite.specTooLong (GF := GF))
    (wp_Flush : EtcdGrove.bufio.Writer.Flush.spec (GF := GF) (hG := hG)) : Msg.MarshalWriteFlush.spec (GF := GF) := by
  intro l v m bw wi J Q Ew sz sent pend err
  wp_start as ⟨#Hl, #Hrep, %Hbnd, #Hwr, Hown, #HQ⟩
  ihave ⟨#Hpb, #Hpio, #Hpbin⟩ := msgPkgDeps_get $$ Hpkg
  wp_auto
  wp_apply hM l v m _ $$ [$Hl $Hrep] as %dsl ⟨-, Hd⟩
  · ipureintro; exact Hbnd
  wp_apply hBW bw wi J Q Ew sz sent pend err dsl _ _ $$ [$Hpkg $Hwr $Hown $HQ $Hd]
    as %e1 ⟨%k, %sent1, %pend1, %Hk, -, Hown⟩
  · ipureintro; exact Hbnd
  obtain ⟨hkl, hks, hkp, hke⟩ := Hk
  wp_apply wp_Flush bw wi J Q Ew sz sent1 pend1 _ $$ [$Hown] as %e2 ⟨%k2, %Hk2, Hown⟩
  obtain ⟨hk2l, hk2e, hk2s⟩ := Hk2
  iapply HΦ
  iexists sent1 ++ pend1.take k2, pend1.drop k2
  iframe Hown
  ipureintro
  refine ⟨hkp.trans (List.prefix_append _ _), ?_, fun h => ?_⟩
  · rw [List.append_assoc, List.take_append_drop, hks]
    exact (List.prefix_append_right_inj _).2 (List.take_prefix _ _)
  · have he1 : e1 = interface.nil := by
      by_cases hne : e1 = interface.nil
      · exact hne
      · rw [(hk2s hne).1] at h; exact absurd h hne
    rw [hk2e h, List.take_length, List.drop_length, hks, hke he1, List.take_length]
    exact ⟨rfl, rfl⟩

end proof

end Perennial.rabia.internal.message

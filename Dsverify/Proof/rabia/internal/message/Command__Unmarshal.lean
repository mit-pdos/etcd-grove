/-
(Ported from dsverify-lab `examples/rabia/proof/Proof/rabia/internal/message/Command__Unmarshal.lean`, run `rabia-r1wake-1`.)

`(*Command).Unmarshal` (message.pb.go 978-1115): decoding `encCmd c` into a zero `Command`
(prover C1).
-/
module

public import Dsverify.Proof.rabia.internal.message.Internal
public import Dsverify.Proof.rabia.internal.message.ObjWire
public import Dsverify.Proof.rabia.internal.message.VarintTac
public import Dsverify.Proof.rabia.internal.message.UnmarshalLemmas

@[expose] public section

namespace Perennial.rabia.internal.message
open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode model bufio

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [package_sem : rabia.internal.message.Assumptions]
variable [IsPkgInit (IProp GF) pkg_id.rabia.internal.message]

/-- A `Command` being decoded: `cmdRep` with an owned slice and its capacity. -/
noncomputable def cmdOwn (v : Command) (c : CmdV) : IProp GF :=
  iprop(⌜v.CliId' = c.cliId ∧ v.CliSeq' = c.cliSeq ∧ v.SvrSeq' = c.svrSeq⌝ ∗
    v.Commands' ↦* c.commands ∗ ownSliceCap GoString v.Commands' (DFrac.own 1))

omit package_sem [IsPkgInit (IProp GF) pkg_id.rabia.internal.message] in
theorem cmdOwn_open (v : Command) (c : CmdV) : cmdOwn (GF := GF) v c ⊢
    ⌜v.CliId' = c.cliId ∧ v.CliSeq' = c.cliSeq ∧ v.SvrSeq' = c.svrSeq⌝ ∗
    v.Commands' ↦* c.commands ∗ ownSliceCap GoString v.Commands' (DFrac.own 1) := by
  unfold cmdOwn; exact .rfl

omit package_sem [IsPkgInit (IProp GF) pkg_id.rabia.internal.message] in
theorem cmdOwn_close (v : Command) (c : CmdV) :
    ⌜v.CliId' = c.cliId ∧ v.CliSeq' = c.cliSeq ∧ v.SvrSeq' = c.svrSeq⌝ ∗
    v.Commands' ↦* c.commands ∗ ownSliceCap GoString v.Commands' (DFrac.own 1) ⊢
    cmdOwn (GF := GF) v c := by
  unfold cmdOwn; exact .rfl

omit package_sem [IsPkgInit (IProp GF) pkg_id.rabia.internal.message] in
theorem cmdOwn_congr (v v' : Command) (c1 c2 : CmdV) (hs : v'.Commands' = v.Commands')
    (hl : c2.commands = c1.commands)
    (hp : v.CliId' = c1.cliId ∧ v.CliSeq' = c1.cliSeq ∧ v.SvrSeq' = c1.svrSeq →
      v'.CliId' = c2.cliId ∧ v'.CliSeq' = c2.cliSeq ∧ v'.SvrSeq' = c2.svrSeq) :
    cmdOwn (GF := GF) v c1 ⊢ cmdOwn v' c2 := by
  unfold cmdOwn
  rw [hs, hl]
  iintro ⟨%H, H2⟩
  iframe
  ipureintro; exact hp H

omit package_sem [IsPkgInit (IProp GF) pkg_id.rabia.internal.message] in
theorem cmdOwn_zero (c : CmdV) : ⊢ cmdOwn (GF := GF) (zeroValDef : Command) (c.upto 0) := by
  unfold cmdOwn
  simp only [CmdV.upto, Nat.not_lt_zero, ite_false, Nat.zero_sub, List.take_zero]
  iintro
  isplitr
  · ipureintro; exact ⟨rfl, rfl, rfl⟩
  isplitr; · iapply ownSlice_nil
  iapply ownSliceCap_nil

set_option maxHeartbeats 4000000 in
theorem Command.Unmarshal.wp_proof : Command.Unmarshal.spec (GF := GF) := by
  intro l sl dq c
  wp_start as ⟨Hl, Hsl⟩
  wp_auto
  ihave %Hlen := ownSlice_len _ _ _ $$ Hsl
  ihave HI : (∃ (s : Nat) (v : Command) (idx : w64),
      "Hl" ∷ l ↦ v ∗ "Hown" ∷ cmdOwn v (c.upto s) ∗ "iNdEx" ∷ iNdEx_ptr ↦ idx ∗
      "%Hs" ∷ ⌜s ≤ 3 + c.commands.length ∧ 0 ≤ sint.Z idx ∧ sint.nat idx ≤ (encCmd c).length ∧
        (encCmd c).drop (sint.nat idx) = ((cmdSegs c).drop s).flatten⌝ : IProp GF)
      $$ [Hl iNdEx]
  · iexists 0, _, _
    iframe
    isplitl []
    · iapply cmdOwn_zero
    ipureintro
    refine ⟨by omega, by decide, by word, ?_⟩
    rw [encCmd_flatten]; rfl
  wp_for HI
  obtain ⟨Hs, Hidx0, Hidxle, Hrest⟩ := Hs
  wp_if_destruct
  · -- an iteration: the next nonempty field
    replace Hif : sint.Z idx < sint.Z sl.len := by first | exact Hif | (revert Hif; simp)
    have hne : ((cmdSegs c).drop s).flatten ≠ [] := by
      rw [← Hrest]; intro h
      rw [List.drop_eq_nil_iff] at h; word
    obtain ⟨j, seg, hj1, hj2, hj3, hj4, hj5, hj6⟩ := next_seg _ _ hne
    rw [cmdSegs_length] at hj2
    rw [← c.upto_of_empty s j hj1 (by omega) hj3]
    rw [hj6] at Hrest
    clear hj6 hj3 hj1 hne Hs
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ 3 ≤ j) with rfl|rfl|rfl|hj6
    · -- field 1: CliId
      simp only [cmdSegs, List.cons_append, List.getElem?_cons_succ, List.getElem?_cons_zero,
        Option.some.injEq] at hj4
      subst hj4
      obtain ⟨hseg, hN⟩ := encScalar_ne_nil hj5
      rw [hseg] at Hrest
      have Hpre0 := Hidx0
      have Hpre : (encCmd c).drop (sint.nat idx) =
          varint 8 ++ (varint (c.cliId.toNat) ++ ((cmdSegs c).drop (0 + 1)).flatten) := by
        rw [Hrest, varint_lt 8 (by decide)]; rfl
      have HNlt : 8 < 2 ^ 64 := by decide
      varint_loop wire (fun a => wire_ptr ↦ BitVec.ofNat 64 a) 8
        (varint (c.cliId.toNat) ++ ((cmdSegs c).drop (0 + 1)).flatten) (encCmd c) as i1
      try rw [show W32 (uint.Z ((8#64) >>> W64 3)) = W32 1 from rfl,
        show ((8#64) &&& W64 7) = W64 0 from rfl]
      try wp_auto
      clear Hpre Hpre0 HNlt Hidx0 Hrest
      have Hpre := Hpost
      have Hpre0 := Hpost0
      have HNlt : c.cliId.toNat < 2 ^ 64 := by have := (c.cliId).isLt; omega
      clear Hpost Hpost0
      varint_loop Hl (fun a => l ↦ Command.mk (BitVec.ofNat 32 a) v.CliSeq' v.SvrSeq' v.Commands') (c.cliId.toNat) (((cmdSegs c).drop (0 + 1)).flatten) (encCmd c) as i2
      rw [w32_ofNat_toNat']
      wp_for_post
      iframe
      iexists 1, _, _
      isplitl [Hl]; · iexact Hl
      isplitl [Hown]
      · iapply cmdOwn_congr v (Command.mk c.cliId v.CliSeq' v.SvrSeq' v.Commands') (c.upto 0) (c.upto 1) rfl (by simp [CmdV.upto])
          (fun h => by simp_all [CmdV.upto])
        iexact Hown
      isplitl [iNdEx]; · iexact iNdEx
      ipureintro
      exact ⟨by omega, Hpost0, Hpostle, Hpost⟩
    · -- field 2: CliSeq
      simp only [cmdSegs, List.cons_append, List.getElem?_cons_succ, List.getElem?_cons_zero,
        Option.some.injEq] at hj4
      subst hj4
      obtain ⟨hseg, hN⟩ := encScalar_ne_nil hj5
      rw [hseg] at Hrest
      have Hpre0 := Hidx0
      have Hpre : (encCmd c).drop (sint.nat idx) =
          varint 16 ++ (varint (c.cliSeq.toNat) ++ ((cmdSegs c).drop (1 + 1)).flatten) := by
        rw [Hrest, varint_lt 16 (by decide)]; rfl
      have HNlt : 16 < 2 ^ 64 := by decide
      varint_loop wire (fun a => wire_ptr ↦ BitVec.ofNat 64 a) 16
        (varint (c.cliSeq.toNat) ++ ((cmdSegs c).drop (1 + 1)).flatten) (encCmd c) as i1
      try rw [show W32 (uint.Z ((16#64) >>> W64 3)) = W32 2 from rfl,
        show ((16#64) &&& W64 7) = W64 0 from rfl]
      try wp_auto
      clear Hpre Hpre0 HNlt Hidx0 Hrest
      have Hpre := Hpost
      have Hpre0 := Hpost0
      have HNlt : c.cliSeq.toNat < 2 ^ 64 := by have := (c.cliSeq).isLt; omega
      clear Hpost Hpost0
      varint_loop Hl (fun a => l ↦ Command.mk v.CliId' (BitVec.ofNat 32 a) v.SvrSeq' v.Commands') (c.cliSeq.toNat) (((cmdSegs c).drop (1 + 1)).flatten) (encCmd c) as i2
      rw [w32_ofNat_toNat']
      wp_for_post
      iframe
      iexists 2, _, _
      isplitl [Hl]; · iexact Hl
      isplitl [Hown]
      · iapply cmdOwn_congr v (Command.mk v.CliId' c.cliSeq v.SvrSeq' v.Commands') (c.upto 1) (c.upto 2) rfl (by simp [CmdV.upto])
          (fun h => by simp_all [CmdV.upto])
        iexact Hown
      isplitl [iNdEx]; · iexact iNdEx
      ipureintro
      exact ⟨by omega, Hpost0, Hpostle, Hpost⟩
    · -- field 3: SvrSeq
      simp only [cmdSegs, List.cons_append, List.getElem?_cons_succ, List.getElem?_cons_zero,
        Option.some.injEq] at hj4
      subst hj4
      obtain ⟨hseg, hN⟩ := encScalar_ne_nil hj5
      rw [hseg] at Hrest
      have Hpre0 := Hidx0
      have Hpre : (encCmd c).drop (sint.nat idx) =
          varint 24 ++ (varint (c.svrSeq.toNat) ++ ((cmdSegs c).drop (2 + 1)).flatten) := by
        rw [Hrest, varint_lt 24 (by decide)]; rfl
      have HNlt : 24 < 2 ^ 64 := by decide
      varint_loop wire (fun a => wire_ptr ↦ BitVec.ofNat 64 a) 24
        (varint (c.svrSeq.toNat) ++ ((cmdSegs c).drop (2 + 1)).flatten) (encCmd c) as i1
      try rw [show W32 (uint.Z ((24#64) >>> W64 3)) = W32 3 from rfl,
        show ((24#64) &&& W64 7) = W64 0 from rfl]
      try wp_auto
      clear Hpre Hpre0 HNlt Hidx0 Hrest
      have Hpre := Hpost
      have Hpre0 := Hpost0
      have HNlt : c.svrSeq.toNat < 2 ^ 64 := by have := (c.svrSeq).isLt; omega
      clear Hpost Hpost0
      varint_loop Hl (fun a => l ↦ Command.mk v.CliId' v.CliSeq' (BitVec.ofNat 32 a) v.Commands') (c.svrSeq.toNat) (((cmdSegs c).drop (2 + 1)).flatten) (encCmd c) as i2
      rw [w32_ofNat_toNat']
      wp_for_post
      iframe
      iexists 3, _, _
      isplitl [Hl]; · iexact Hl
      isplitl [Hown]
      · iapply cmdOwn_congr v (Command.mk v.CliId' v.CliSeq' c.svrSeq v.Commands') (c.upto 2) (c.upto 3) rfl (by simp [CmdV.upto])
          (fun h => by simp_all [CmdV.upto])
        iexact Hown
      isplitl [iNdEx]; · iexact iNdEx
      ipureintro
      exact ⟨by omega, Hpost0, Hpostle, Hpost⟩
    · -- field 4: a command
      have hjc : j - 3 < c.commands.length := by omega
      have hseg : seg = encBytes 0x22 (c.commands[j - 3]) := by
        simp only [cmdSegs, List.getElem?_append_right (by simp; omega : [encScalar 0x08 c.cliId.toNat,
          encScalar 0x10 c.cliSeq.toNat, encScalar 0x18 c.svrSeq.toNat].length ≤ j),
          List.getElem?_map] at hj4
        simp only [List.length_cons, List.length_nil, Nat.reduceAdd, List.getElem?_eq_getElem hjc,
          Option.map_some, Option.some.injEq] at hj4
        exact hj4.symm
      subst hseg
      generalize hcmd : c.commands[j - 3] = cmd at Hrest
      simp only [encBytes] at Hrest
      have Hpre0 := Hidx0
      have Hpre : (encCmd c).drop (sint.nat idx) =
          varint 34 ++ (varint cmd.length ++ cmd ++ ((cmdSegs c).drop (j + 1)).flatten) := by
        rw [Hrest, varint_lt 34 (by decide)]; simp
      have HNlt : 34 < 2 ^ 64 := by decide
      varint_loop wire (fun a => wire_ptr ↦ BitVec.ofNat 64 a) 34
        (varint cmd.length ++ cmd ++ ((cmdSegs c).drop (j + 1)).flatten) (encCmd c) as i1
      try rw [show W32 (uint.Z ((34#64) >>> W64 3)) = W32 4 from rfl,
        show ((34#64) &&& W64 7) = W64 2 from rfl]
      try wp_auto
      clear Hpre Hpre0 HNlt Hidx0 Hrest
      have Hpre := Hpost
      have Hpre0 := Hpost0
      have HNlt : cmd.length < 2 ^ 64 := by
        have := congrArg List.length Hpre
        simp only [List.length_drop, List.length_append] at this; word
      clear Hpost Hpost0
      varint_loop stringLen (fun a => stringLen_ptr ↦ BitVec.ofNat 64 a) cmd.length
        (cmd ++ ((cmdSegs c).drop (j + 1)).flatten) (encCmd c) as i2
      have HLlt : sint.nat i2 + cmd.length ≤ (encCmd c).length := by
        have := congrArg List.length Hpost
        simp only [List.length_drop, List.length_append] at this; omega
      wp_if_destruct
      · exfalso; word
      wp_if_destruct
      · exfalso; word
      wp_if_destruct
      · exfalso; word
      ihave %Hwf := ownSlice_wf _ _ _ $$ Hsl
      have Hhi : sint.nat (i2 + BitVec.ofNat 64 cmd.length) = sint.nat i2 + cmd.length := by word
      rw [if_pos ⟨Hpost0, by word, by word⟩]
      have Hb : 0 ≤ sint.Z i2 ∧ sint.Z i2 ≤ sint.Z (i2 + BitVec.ofNat 64 cmd.length) ∧
          sint.Z (i2 + BitVec.ofNat 64 cmd.length) ≤ sint.Z sl.len := ⟨Hpost0, by word, by word⟩
      icases (ownSlice_slice _ _ sl dq (encCmd c) Hb).1 $$ Hsl with ⟨Hsl1, Hsl2, Hsl3⟩
      rw [Hhi, subslice_of_drop' _ _ _ _ Hpost]
      wp_apply wp_bytes_to_string $$ Hsl2 as Hsl2
      ihave Hsl := (ownSlice_slice _ _ sl dq (encCmd c) Hb).2 $$ [Hsl1 Hsl2 Hsl3]
      · rw [Hhi, subslice_of_drop' _ _ _ _ Hpost]; iframe
      wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType go.string))))
        (Val (LiteralValueV _)))
      iapply wp_slice_literal (V := GoString) (t := go.string) [cmd]
      wp_auto
      rw [show go.arrayLiteralSize
        [KeyedElement none (ElementExpression go.string #cmd)] = 1 from rfl]
      isplitl []
      · ipureintro; rfl
      iintro %lit_ptr ⟨Hlit, Hlitcap⟩
      icases cmdOwn_open _ _ $$ Hown with ⟨%Hown, Hcmds, Hcmdscap⟩
      wp_apply wp_slice_append $$ [Hcmds Hcmdscap Hlit] as %ns ⟨Hcmds, Hcmdscap, -⟩
      · iframe
      wp_auto
      wp_for_post
      iframe
      iexists j + 1, _, _
      iframe
      isplitl [Hcmds Hcmdscap]
      · iapply cmdOwn_close
        have e3 : (c.upto (j + 1)).commands = (c.upto j).commands ++ [cmd] := by
          simp only [CmdV.upto, show j + 1 - 3 = (j - 3) + 1 by omega, List.take_add_one,
            List.getElem?_eq_getElem hjc, hcmd, Option.toList_some]
        rw [e3]
        iframe
        ipureintro
        simp only [CmdV.upto] at Hown ⊢
        simp only [show 0 < j by omega, show 1 < j by omega, show 2 < j by omega,
          show 0 < j + 1 by omega, show 1 < j + 1 by omega,
          show 2 < j + 1 by omega, ite_true] at Hown ⊢
        exact Hown
      ipureintro
      refine ⟨by omega, by word, by word, ?_⟩
      rw [Hhi, ← List.drop_drop, Hpost, List.drop_left]
  · -- the end
    replace Hif : ¬ sint.Z idx < sint.Z sl.len := by first | exact Hif | (revert Hif; simp)
    have hnil : ((cmdSegs c).drop s).flatten = [] := by
      rw [← Hrest, List.drop_eq_nil_iff]; word
    have ho : c.upto s = c := by
      have := c.upto_of_empty s (3 + c.commands.length) Hs (Nat.le_refl _)
        (fun i h1 h2 => rest_nil _ _ hnil i h1 (by rw [cmdSegs_length]; exact h2))
      rw [c.upto_all] at this; exact this.symm
    rw [ho]
    unfold cmdOwn
    icases Hown with ⟨%H, H3, -⟩
    ipersist H3
    wp_if_destruct
    · exfalso; word
    wp_end
    iexists v
    iframe
    unfold cmdRep
    isplitl []; · ipureintro; exact H
    iexact H3

end proof
end Perennial.rabia.internal.message

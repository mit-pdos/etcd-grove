/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/ReplyChan.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
The reply channel (swift/replychan.go): `NewReplyChan`'s goroutine, `stop`, `reply`
(notes/prove-swift.md §12).

The goroutine of the epoch of ballot `b0` loops on a `select` over `exit` and `args`:
* `exit`: hands back on `ok` its reading right of `ballot` (or the cell's unused claim token)
  and `historySize`, and returns;
* `args`: the first message's `cellFilled` lets it claim its reading right; the leader's
  `MReply` (`optExec`, `Id == leader()`) is sent to the client with the witness the message
  carries (`replyOk`); the `MAccept` branch is dead (the `GPropose` has `Proxy = false`); the
  next history slot (`historySize % len(history)`, then `+ 1`) goes back on the descriptor's
  channel.

Hypotheses (open): `clientChecksum`'s spec and `MReply`'s `Marshal` (`marshalOk`).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.NewSpecs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.LeaderM
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.Deliver
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.ReplyOk
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.ReplyChanDefs

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section specs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps]
variable [swift.Assumptions]

end specs

section proof
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps]
variable [swift.Assumptions] [replica.Assumptions]

set_option goose.wp.extras true

theorem swift.NewReplyChan.wp_proof (wp_cc : swift.clientChecksum.specR (hG := hG))
    (hmar : swift.MReply.marshalH (hG := hG))
    (wp_send : replica.Sender.SendToClient.spec (hG := hG))
    (wp_Leader : replica.Leader.spec) :
    swift.NewReplyChan.specI (hG := hG) := by
  intro rp rr hsl γ γc γm γl b0
  wp_start as ⟨#HReplica, #HShutdown, #Hhist, #Hcell, Hclaim, %Hn⟩
  wp_auto
  wp_apply chan.wp_make2 (V := Unit) (W64 1) as %ok %γok ⟨#Hok, %Hokcap, Hokown⟩
  · ipureintro; decide
  wp_apply chan.wp_make2 (V := Unit) (W64 2) as %ex %γex ⟨#Hex, %Hexcap, Hexown⟩
  · ipureintro; decide
  wp_apply chan.wp_make2 (V := Loc) (W64 2000000) as %ar %γa ⟨#Har, %Harcap, Harown⟩
  · ipureintro; decide
  try wp_auto
  ipersist rc
  ipersist r
  ipersist «$r0»
  iapply fupd_wp
  imod start_bag (fun _ : Unit => swift.replyBack rp γl b0) (ChanState.Buffered []) ok γok
    (by trivial) $$ [$Hok] [Hokown] with #Hbok
  · iexact Hokown
  imod start_bag (fun _ : Unit => iprop(True)) (ChanState.Buffered []) ex γex
    (by trivial) $$ [$Hex] [Hexown] with #Hbex
  · iexact Hexown
  imod start_bag (fun a : Loc => swift.replyArgP γ γc γm rp γl b0 a) (ChanState.Buffered []) ar γa
    (by trivial) $$ [$Har] [Harown] with #Hbar
  · iexact Harown
  imodintro
  wp_apply wp_fork $$ [Hclaim]
  · ihave #R2 := «$r0»
    iStructNamedPrefix R2 "RC"
    wp_auto_lc 2
    ihave HL : (swift.replyLoopSt rp γl b0 ∗ "Hlc1" ∷ £ 1 ∗ "Hlc2" ∷ £ 1 : IProp netDistGF)
      $$ [Hclaim Hlc1 Hlc2]
    · iframe; iunfold swift.replyLoopSt; iunfold swift.replyBack; iright; iexact Hclaim
    wp_for HL
    icases HL with ⟨HL, Hlc1, Hlc2⟩
    wp_apply_core chan.wp_select_blocking
    iapply BigAndL.bigAndL_cons.2
    isplit
    · -- `exit`
      iapply swift.bag_clauseT $$ Hlc1 Hlc2 Hbex
      inext
      iintro %v -
      wp_auto
      iunfold swift.replyLoopSt at HL
      wp_apply wp_bag_send γok ok () (fun _ : Unit => swift.replyBack rp γl b0) $$ [$Hbok HL]
      · iexact HL
      wp_for_post
      itrivial
    iapply BigAndL.bigAndL_cons.2
    isplit
    · -- `args`
      iapply swift.bag_clauseT $$ Hlc1 Hlc2 Hbar
      inext
      iintro %a Ha
      wp_auto_lc 2
      iunfold swift.replyArgP at Ha
      icases Ha with ⟨%ra, %D, %Hs, %vals, %γf, %F, %rr', %s, %p, %w, %mu, %addr, %N, %me, %γw,
        %γs, %csv, %oe, Ha, #Hfilled, Hdep, Hhs', #Hval, %Hwf, #HRep', #HisR, #Hsnd, #Hsbag, #Hcs,
        %Hcodes, #Hoe, #Hprop, #Hcid, #Hfin, #HF, #Hrok⟩
      icombine HReplica HRep' gives %Hrr
      subst Hrr
      iunfold swift.replyLoopSt at HL
      iunfold swift.replyBack at HL
      -- the reading right and `historySize`: claimed at the first message
      iapply fupd_wp
      ihave Hb : |={⊤}=> swift.replyCellRes rp b0 $$ [HL]
      · icases HL with (Hb | Hk)
        · imodintro; iexact Hb
        · imod swift.cell_claim swift.replyCellN ⊤ (by simp) γl (swift.replyCellRes rp b0)
            $$ [$Hcell $Hk $Hfilled] with >Hb
          imodintro; iexact Hb
      imod Hb
      iunfold swift.replyCellRes at Hb
      icases Hb with ⟨Hb, %n', Hhs, %Hn'⟩
      imodintro
      iStructNamedPrefix Ha "A"
      ihave #P2 := Hprop
      iStructNamedPrefix P2 "P"
      ihave #R2 := HisR
      iunfold replica.isReplica at R2
      icases R2 with ⟨%lg, %cfgp, %tbl, %pc, %fr, %nid, %ents, %γpc, %pwsl, %alsl, %latsl, %pws,
        %cwm, -, -, #HN, #HId, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, %HNp, -⟩
      have hN : 1 ≤ N ∧ N ≤ 7 := by
        obtain ⟨_, h1, h2, h3⟩ := HNp; refine ⟨?_, h3⟩; have := Int.lt_of_le_of_lt h1 h2; omega
      ihave #C2 := Hcs
      iStructNamedPrefix C2 "C"
      wp_auto
      cases oe
      · -- no `optExec`: no reply
        wp_auto
        have hl0 : ¬ sint.Z hsl.len = 0 := by rw [Hn]; decide
        isimp only [hl0, ↓reduceIte]
        wp_auto
        have hsb := swift.srem_bounds n' hsl.len Hn'.1 (by rw [Hn]; decide)
        have hslot : swift.slotIn (BitVec.srem n' hsl.len) := by
          unfold swift.slotIn; rw [Hn] at hsb; exact hsb
        ihave HFv : F (interface.mkOk go.int #(BitVec.srem n' hsl.len + W64 1 - W64 1)) $$ []
        · iapply HF; ipureintro
          rw [BitVec.add_sub_cancel]; exact hslot
        wp_apply wp_bag_send (t := go.InterfaceType []) γf ra.finish' _ F $$ [$Hfin $HFv]
        wp_for_post
        isplitl [Hhs Hb]
        · iapply swift.replyLoopSt_intro rp γl b0 _ (swift.slot_succ _ hslot)
          iframe Hhs; unfold swift.replyRes; iexact Hb
        iframe
      wp_auto
      iunfold swift.replyRes at Hb
      wp_apply swift.Replica.wp_leader wp_Leader rp rr b0 _ N hN $$ [$Hb $HReplica $HN] as Hb
      by_cases hld : me = BitVec.srem b0 (W32 (sint.Z (W64 (N : Int))))
      · isimp only [hld, _root_.decide_true]
        wp_auto
        wp_apply wp_cc ra.hs' ra.dep' Hs D (DFrac.own 1) (DFrac.own 1) $$ [$Hhs' $Hdep] as %csl ⟨Hhs', Hdep, %d, Hcsl, #Hdh, %Hd⟩
        · ipureintro; exact ⟨Hwf.1, Hwf.2.1, Hwf.2.2.1⟩
        wp_method_call
        wp_call
        wp_auto
        have hwf : sp.Msg.wf (.reply me b0 (toCmdId ra.cmdId') (Hs ++ [d]) vals) := by
          refine ⟨⟨?_, ?_⟩, Hwf.2.2.2⟩
          · simp; omega
          · intro h hh; simp at hh; rcases hh with hh | hh
            · exact Hwf.1.2 h hh
            · subst hh; exact Hd
        wp_apply wp_send rr γ γc γm γw N me γs s ra.cmdId'.ClientId'
          (interface.mkOk (go.GoType.PointerType swift.MReply.ty) #«$r0_ptr»)
          (.reply me b0 (toCmdId ra.cmdId') (Hs ++ [d]) vals) csv.replyRPC'
          iprop(«$r0_ptr» ↦ swift.MReply.mk me b0 ra.cmdId' csl ra.val' ∗
            csl ↦* (Hs ++ [d]).map swift.handler.shashOf ∗ ra.val' ↦*□ vals)
          $$ [$HisR $Hsbag «$r0» Hcsl]
        · unfold replica.toSend
          isplitl
          · isplitr
            · iapply (hmar «$r0_ptr» me b0 ra.cmdId' csl ra.val' (Hs ++ [d]) vals hwf)
            isplitl [«$r0» Hcsl]
            · iframe; iexact Hval
            isplitr
            · iunfold swift.replyOk at Hrok
              iapply Hrok
              · ipureintro; exact hld
              iexact Hdh
            isplitr
            · unfold replica.freeOk; ileft; ipureintro; rfl
            ipureintro
            refine ⟨hwf, ?_⟩
            rw [Hcodes.2.2.2.2.2.2.1]; rfl
          ipureintro
          simp [sp.Msg.isToClient, toCmdId]
        have hl0 : ¬ sint.Z hsl.len = 0 := by rw [Hn]; decide
        isimp only [hl0, ↓reduceIte]
        wp_auto
        have hsb := swift.srem_bounds n' hsl.len Hn'.1 (by rw [Hn]; decide)
        have hslot : swift.slotIn (BitVec.srem n' hsl.len) := by
          unfold swift.slotIn; rw [Hn] at hsb; exact hsb
        ihave HFv : F (interface.mkOk go.int #(BitVec.srem n' hsl.len + W64 1 - W64 1)) $$ []
        · iapply HF; ipureintro
          rw [BitVec.add_sub_cancel]; exact hslot
        wp_apply wp_bag_send (t := go.InterfaceType []) γf ra.finish' _ F $$ [$Hfin $HFv]
        wp_for_post
        isplitl [Hhs Hb]
        · iapply swift.replyLoopSt_intro rp γl b0 _ (swift.slot_succ _ hslot)
          iframe Hhs; unfold swift.replyRes; iexact Hb
        iframe

      · isimp only [hld, decide_false]
        wp_auto
        have hl0 : ¬ sint.Z hsl.len = 0 := by rw [Hn]; decide
        isimp only [hl0, ↓reduceIte]
        wp_auto
        have hsb := swift.srem_bounds n' hsl.len Hn'.1 (by rw [Hn]; decide)
        have hslot : swift.slotIn (BitVec.srem n' hsl.len) := by
          unfold swift.slotIn; rw [Hn] at hsb; exact hsb
        ihave HFv : F (interface.mkOk go.int #(BitVec.srem n' hsl.len + W64 1 - W64 1)) $$ []
        · iapply HF; ipureintro
          rw [BitVec.add_sub_cancel]; exact hslot
        wp_apply wp_bag_send (t := go.InterfaceType []) γf ra.finish' _ F $$ [$Hfin $HFv]
        wp_for_post
        isplitl [Hhs Hb]
        · iapply swift.replyLoopSt_intro rp γl b0 _ (swift.slot_succ _ hslot)
          iframe Hhs; unfold swift.replyRes; iexact Hb
        iframe
    iapply BigAndL.bigAndL_nil.2
    itrivial
  try wp_auto
  iapply HΦ
  unfold swift.replyChanH
  iexists «$v0_ptr», ok, ex, ar, γok, γex, γa
  isplitr
  · iexact «$r0»
  isplitr
  · iexact Hbar
  isplitr
  · iexact Hbex
  isplitr
  · iexact Hbok
  iexact Hcell

theorem swift.replyChan.stop.wp_proof : swift.replyChan.stop.specR (hG := hG) := by
  intro γ γc γm rp γl b0 rc
  wp_start as Hrc
  unfold swift.replyChanH
  icases Hrc with ⟨%rep, %ok, %ex, %ar, %γok, %γex, %γa, #Hrc, #Har, #Hex, #Hok, #Hcell⟩
  ihave #R2 := Hrc
  iStructNamedPrefix R2 "RC"
  wp_auto
  wp_apply wp_bag_send (t := go.StructType []) γex ex () (fun _ : Unit => iprop(True)) $$ [$Hex]
  wp_apply wp_bag_receive (t := go.StructType []) γok ok (fun _ : Unit => swift.replyBack rp γl b0)
    $$ [$Hok] as %u Hb
  try wp_auto
  iapply HΦ
  iexact Hb

theorem swift.replyChan.reply.wp_proof : swift.replyChan.reply.specR (hG := hG) := by
  intro γ γc γm rp γl b0 rc d γd MP dv x v
  wp_start as ⟨#Hrc, Hd, #Hctx⟩
  ihave #Hctx2 := Hctx
  iunfold swift.replyCtx at Hctx2
  icases Hctx2 with ⟨%Hs, %vals, %rr, %s, %p, %w, %mu, %addr, %N, %me, %γw, %γs, %csv, %oe,
    #Hfilled, %Hpure, #Hval, #HRep, #HisR, #Hsnd, #Hsbag, #Hcs, %Hcodes, #Hoe, #Hprop, #Hcid, #HMP,
    #Hrok⟩
  ihave #Hrc2 := Hrc
  iunfold swift.replyChanH at Hrc2
  icases Hrc2 with ⟨%rep, %ok, %ex, %ar, %γok, %γex, %γa, #Hrcs, #Har, #Hex, #Hok, #Hcell⟩
  iStructNamedPrefix Hrcs "RC"
  iunfold swift.descF at Hd
  icases Hd with ⟨Hph, Hcmd, #Hvs, Hdep, #HD, Hhs, #HHs, Hprop', Hseq, Hmsgs, #Hmb, #Hsucc, %Hop⟩
  ihave %HDl := ownSlice_len _ _ _ $$ HD
  ihave %HHl := ownSlice_len _ _ _ $$ HHs
  try wp_auto
  wp_apply (wp_slice_make2 (V := swift.CommandId) dv.dep.len) as %dsl ⟨Hdsl, -⟩
  · ipureintro; exact HDl.2
  wp_apply (wp_slice_copy (V := swift.CommandId)) $$ [$Hdsl $HD] as %n1 ⟨%Hn1, Hdsl, -⟩
  try wp_auto
  wp_apply (wp_slice_make2 (V := swift.SHash) dv.hs.len) as %hsl ⟨Hhsl, -⟩
  · ipureintro; exact HHl.2
  try wp_auto
  wp_apply (wp_slice_copy (V := swift.SHash)) $$ [$Hhsl $HHs] as %n2 ⟨%Hn2, Hhsl, -⟩
  try wp_auto
  isimp only [swift.copy_all _ _ _ HDl.1] at Hdsl
  isimp only [swift.copy_all _ _ _ HHl.1] at Hhsl
  obtain ⟨hHs, hwf, hl1, hl2, hl3⟩ := Hpure
  isimp only [hHs] at Hhsl
  ihave HA : swift.replyArgP γ γc γm rp γl b0 «$v_ptr» $$ [«$v» Hdsl Hhsl]
  · iunfold swift.replyArgP
    iexists _, dv.D, Hs, vals, γd, MP, rr, s, p, w, mu, addr, N, me, γw, γs, csv, oe
    isplitl [«$v»]; · iexact «$v»
    isplitr; · iexact Hfilled
    isplitl [Hdsl]; · iexact Hdsl
    isplitl [Hhsl]; · iexact Hhsl
    isplitr; · iexact Hval
    isplitr; · ipureintro; exact ⟨hwf, hl1, hl2, hl3⟩
    isplitr; · iexact HRep
    isplitr; · iexact HisR
    isplitr; · iexact Hsnd
    isplitr; · iexact Hsbag
    isplitr; · iexact Hcs
    isplitr; · ipureintro; exact Hcodes
    isplitr; · iexact Hoe
    isplitr; · iexact Hprop
    isplitr; · iexact Hcid
    isplitr; · iexact Hmb
    isplitr; · iexact HMP
    iexact Hrok
  wp_apply wp_bag_send (t := go.GoType.PointerType swift.replyArgs.ty) γa ar «$v_ptr»
    (fun a : Loc => swift.replyArgP γ γc γm rp γl b0 a) $$ [$Har $HA]
  try wp_auto
  iapply HΦ
  unfold swift.descF
  iframe
  iframe Hvs HD HHs Hmb Hsucc
  ipureintro; exact Hop

/-- **`reply` on the reply-channel object** (SWC-2, round S1; `reply.specE`, ReplyDefs.lean):
`replyCtx` from `RCh` (the channel, its cell, the sending context), `deliver`'s replica facts, the
descriptor's `replyPre`, and `replyOk` from the execution witness (`swift.replyOk_of`). -/
theorem swift.replyChan.reply.wp_proofE : swift.replyChan.reply.specE (hG := hG) := by
  intro γ γc γm γl γw rp rr N me bw fr l oe rc d γd MP dv x v
  iintro %Φ ⟨#HRC, Hd, #HRep, #HisR, #Hoe, #Hinv, #Hcfg, %Hb, #Hwit, #Hpre, #HMP⟩ HΦ
  iunfold swift.RCh at HRC
  icases HRC with ⟨%γl', %rr', %s, %N', %γs, %csv, #Hrch, #Hfilled, #HRep', #HN', #Hsnd, #Hsbag,
    #Hcs, %Hcodes⟩
  icombine HRep HRep' gives %Hrr
  subst Hrr
  ihave #R2 := HisR
  iunfold replica.isReplica at R2
  icases R2 with ⟨%lg, %cfgp, %tbl, %pc, %fr', %nid, %ents, %γpc, %pwsl, %alsl, %latsl, %pws,
    %cwm, -, -, #HN, #HId, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, %HNp, -⟩
  icombine HN HN' gives %HNeq
  have hN : 1 ≤ N ∧ N ≤ 7 := by
    obtain ⟨_, h1, h2, h3⟩ := HNp; refine ⟨?_, h3⟩; have := Int.lt_of_le_of_lt h1 h2; omega
  have hNN : N' = N := by
    have h7 := Hcodes.2
    have : sint.Z (W64 (N : Int)) = sint.Z (W64 (N' : Int)) := by rw [HNeq]
    have e1 : sint.Z (W64 (N : Int)) = N := by word
    have e2 : sint.Z (W64 (N' : Int)) = N' := by word
    omega
  subst hNN
  iunfold swift.replyPre at Hpre
  icases Hpre with ⟨%Hs, %p, %w, %mu, %addr, #Hprop, #Hcid, %Hhs, #Hpaths⟩
  iapply fupd_wp
  imod (swift.replyOk_of γ γc γm γl N' fr l me bw x dv.D Hs v Hb.1 Hb.2 hN)
    $$ [Hinv Hcfg Hwit Hpaths] with ⟨%vals, #Hvals, %Hvl, #Hrok⟩
  · iframe Hinv Hcfg Hwit Hpaths
  imodintro
  iapply (swift.replyChan.reply.wp_proof γ γc γm rp γl' bw rc d γd MP dv x v) $$ [Hd] HΦ
  iframe Hrch Hd
  iunfold swift.replyCtx
  iexists Hs, vals, rr, s, p, w, mu, addr, N', me, γw, γs, csv, oe
  iframe Hfilled Hvals HRep HisR Hsnd Hsbag Hcs Hoe Hprop Hcid HMP Hrok
  ipureintro
  exact ⟨⟨Hhs.1, Hhs.2.1, Hhs.2.2.1, Hhs.2.2.2, Hvl⟩, Hcodes.1⟩

end proof

end Perennial.github_com.imdea_software.swiftpaxos

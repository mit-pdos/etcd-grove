/-
Package `proxy`: `internalSendMessage` and `startOutgoingLinks` (the senders of answers to the
client), over `sharedNet`'s writers (`SharedNet.lean`).
-/
module

public import Dsverify.Proof.raxos.Proxy.NetWriter

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.raxos


open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open Perennial.raxos.pure Perennial.raxos.msg
open raxos.replica.src

theorem ansStream_snoc (k : Nat) (L : List Batch) (b : Batch) :
    ansStream k (L ++ [b]) = ansStream k L ++ [W8 1] ++
      (le8 (encBatch b).length ++ encBatch b) := by
  simp [ansStream, frame, List.append_assoc]

section ghost
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [π : NetProtoGS] [qv : hyp.QpVocab GF]

/-- The answers `L` (fit, each one result with its `opAns`) and an allowed prefix are what a
client's port allows. -/
theorem clientIn_of_ans (γ : QNames) (c k : Nat) (cid : Nat) (L : List Batch)
    (bs : List w8) (hk : k < 2 ^ 16) (hL : ∀ b ∈ L, batchFit b)
    (hp : bs <+: ansStream k L) :
    ([∗list] b ∈ L, ∃ r, ⌜b.cmds = [r]⌝ ∗ opAns (GF := GF) γ b.id r) ⊢
      clientInProto γ c cid bs := by
  iintro HL
  unfold clientInProto
  iexists k, L
  iframe HL
  ipureintro
  exact ⟨hk, by simpa [ansStream] using hp, hL⟩

/-- Claim writer `w` into the peer mutex's body (holding it): the writer, and the way back. -/
theorem peerR_claim (γ : QNames) (k c : Nat) (γp : GName) (w : Loc) :
    ⊢ inv wN iprop(wSlot (GF := GF) γ k c w ∨ ghostMapElem γp w DFrac.discard ()) -∗ £ 1 -∗
      peerR γ k c γp ={⊤}=∗ wSlot γ k c w ∗ (wSlot γ k c w -∗ peerR γ k c γp) := by
  iintro #Hinv Hlc HR
  unfold peerR
  icases HR with ⟨%C, Ha, Hm⟩
  cases hC : C.lookup w with
  | some u =>
    icases (BigSepM.bigSepM_lookup_acc (Φ := fun w' (_ : Unit) => wSlot (GF := GF) γ k c w')
      (show PartialMap.get? C w = some u from hC)).1 $$ Hm with ⟨Hw, Hback⟩
    imodintro
    iframe Hw
    iintro Hw
    iexists C
    iframe Ha
    iapply Hback $$ Hw
  | none =>
    iinv Hinv with Hi Hclose
    imod lc_fupd_elim_later $$ Hlc Hi with Hi
    icases Hi with (Hw | #He)
    · imod ghost_map_insert_persist w () hC $$ Ha with ⟨Ha, #He⟩
      imod Hclose $$ [] with -
      · inext; iright; iexact He
      imodintro
      iframe Hw
      iintro Hw
      iexists C.insert w ()
      iframe Ha
      iapply (BigSepM.bigSepM_insert (Φ := fun w' (_ : Unit) => wSlot (GF := GF) γ k c w')
        (show PartialMap.get? C w = none from hC)).2
      iframe Hw Hm
    · icombine Ha He gives %Hl
      rw [hC] at Hl
      cases Hl

end ghost

section proofs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [π : NetProtoGS] [qv : hyp.QpVocab GF]
variable [raxos.replica.src.Assumptions] [raxos.proto.client.Assumptions]
variable [_root_.Perennial.bufio.Assumptions] [pb : hyp.PbHyp GF]

/-- The answer's frame, once encoded into `enc` (fit), sent on a healthy writer: the code
byte, the length and the encoding, then the flush; the writer's slot is restored. -/
theorem internalSendMessage_proof : internalSendMessage.spec (GF := GF) (hG := hG) := by
  intro γ c k pr peer rp l cl x r
  wp_start as ⟨#Hsh, %Hrp, #Hrep, #Hans⟩
  obtain ⟨hcode, hobj⟩ := Hrp
  ihave ⟨#Hf, #Hc, #Hch, #Hl, #Hn⟩ := proxyShared_net $$ Hsh
  iunfold sharedFacts at Hf
  icases Hf with ⟨%Hk3, -⟩
  have hk : k < 2 ^ 16 := by have := Hk3.1.1; omega
  unfold sharedNet
  icases Hn with ⟨%rm, %wm, %bm, %cm, %rt, %rp1, %cb0, %BM, %γw, %CM, %RT, #Hsa, #Hrm, #Hninv,
    #Hwm, #HWmu, #Hbm, #HBM, %HBM21, #Hmus, #Hcm, #HCM, %HCM21, #Hrt, #HRT, %HRT1, #Hrp1⟩
  wp_auto
  wp_apply sync.Mutex.wp_Lock $$ [$HWmu] as ⟨Hlk, HW⟩
  iunfold writersR at HW
  icases HW with ⟨%W, HWm, #HWs⟩
  wp_apply wp_map_lookup1 $$ HWm as HWm
  wp_apply sync.Mutex.wp_Unlock $$ [$HWmu $Hlk HWm]
  · iunfold writersR; iexists W; iframe HWm HWs
  cases hW : W !! peer with
  | none =>
    simp only [Option.getD_none]
    wp_auto
    wp_end
  | some w =>
    simp only [Option.getD_some]
    ihave #Hpub := (BigSepM.bigSepM_lookup_acc (Φ := fun p w => wPub (GF := GF) γ k BM γw p w)
      (show PartialMap.get? W peer = some w from hW)).1 $$ HWs
    icases Hpub with ⟨Hpub, -⟩
    iunfold wPub at Hpub
    icases Hpub with ⟨%mu, %HBMp, #Hwinv⟩
    wp_if_destruct
    · wp_end
    -- P4: the answer is encoded first, into a fresh `msgBuffer`
    ihave Hmb : ownMB enc_ptr [] $$ [enc]
    · iunfold ownMB
      iexists slice.nil
      iframe enc
      isplitl
      · iapply ownSlice_nil
      · iapply ownSliceCap_nil
    rw [hobj]
    wp_auto
    wp_apply marshal_buf l DFrac.discard (Batch.mk x (clientName cl) [r]) enc_ptr [] $$ [$Hrep $Hmb]
      as %e0 ⟨-, %bs', Hmb, %Hm⟩
    rcases e0 with ei | _
    · wp_auto
      wp_end
    obtain ⟨hfit, hbs'⟩ := Hm rfl
    simp only [List.nil_append] at hbs'
    subst hbs'
    wp_auto
    ihave #Hmu := (BigSepM.bigSepM_lookup_acc
      (Φ := fun p mu => sync.isMutex (GF := GF) mu (peerR γ k (cOf p) (γw p)))
      (show PartialMap.get? BM peer = some mu from HBMp)).1 $$ Hmus
    icases Hmu with ⟨#Hmu, -⟩
    wp_apply wp_map_lookup1 $$ HBM as -
    simp only [HBMp, Option.getD_some]
    wp_apply (lc := 1) sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlk, HR⟩
    imod peerR_claim γ k (cOf peer) (γw peer) w $$ Hwinv Hlc1 HR with ⟨Hslot, Hback⟩
    iunfold wSlot at Hslot
    icases Hslot with ⟨%wi, %cid, %Ew, %sent, %pend, %err, Hown, Hst⟩
    simp only [hcode]
    rcases err with ei | _
    · wp_apply (EtcdGrove.bufio.Writer.WriteByte.wp_proof EtcdGrove.bufio.Writer.Flush.wp_proof) w wi _ _ Ew 4096 sent pend
          (GoInterface.ok ei) (W8 1) $$ [Hown] as %e1 ⟨%sent1, %pend1, %Hwb, Hown⟩
      · iframe Hown; iintro %h; cases h
      obtain ⟨rfl, -, -⟩ := Hwb.2.2.2.1 (by intro h; cases h)
      wp_auto
      wp_apply wp_map_lookup1 $$ HBM as -
      simp only [HBMp, Option.getD_some]
      wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlk Hown Hback]
      · iapply Hback; iunfold wSlot; iexists wi, cid, Ew, sent1, pend1, GoInterface.ok ei
        iframe Hown; ileft; ipureintro; simp
      wp_end
    icases Hst with (%Hne | ⟨%L, %HL, #HLs⟩)
    · exact (Hne rfl).elim
    have HL' : ∀ b ∈ L ++ [(Batch.mk x (clientName cl) [r])], batchFit b := by
      intro b hb; simp at hb; rcases hb with h | rfl; exact HL.2 b h; exact hfit
    ihave #HLs' : [∗list] b ∈ L ++ [(Batch.mk x (clientName cl) [r])], ∃ r', ⌜b.cmds = [r']⌝ ∗
        opAns (GF := GF) γ b.id r' $$ []
    · iapply BigSepL.bigSepL_snoc.2
      iframe HLs
      iexists r
      iframe Hans
      ipureintro; rfl
    wp_apply (EtcdGrove.bufio.Writer.WriteByte.wp_proof EtcdGrove.bufio.Writer.Flush.wp_proof) w wi _ _ Ew 4096 sent pend GoInterface.nil
        (W8 1) $$ [Hown] as %e1 ⟨%sent1, %pend1, %Hwb, Hown⟩
    · iframe Hown
      iintro %_
      imodintro
      iapply clientIn_of_ans γ (cOf peer) k cid _ _ hk HL'
        (by rw [ansStream_snoc, ← HL.1]; simp [List.append_assoc])
      iexact HLs'
    rcases e1 with ei | _
    · wp_auto
      wp_apply wp_map_lookup1 $$ HBM as -
      simp only [HBMp, Option.getD_some]
      wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlk Hown Hback]
      · iapply Hback; iunfold wSlot; iexists wi, cid, Ew, sent1, pend1, GoInterface.ok ei
        iframe Hown; ileft; ipureintro; simp
      wp_end
    have H1 : sent1 ++ pend1 = sent ++ pend ++ [W8 1] := Hwb.2.1 rfl
    iunfold ownMB at Hmb
    icases Hmb with ⟨%s, Hm, Hs, -⟩
    wp_auto
    wp_apply (EtcdGrove.bufio.Writer.Write.wp_proof EtcdGrove.bufio.Writer.Flush.wp_proof) w wi _ _ Ew 4096 sent1 pend1 GoInterface.nil s
        (DFrac.own 1) _ $$ [Hown Hs] as %nn %e2 ⟨%k2, %sent2, %pend2, %Hk2, -, Hown⟩
    · iframe Hown Hs
      iintro %_
      imodintro
      iapply clientIn_of_ans γ (cOf peer) k cid _ _ hk HL'
        (by rw [H1, ansStream_snoc, ← HL.1]; simp [List.append_assoc])
      iexact HLs'
    rcases e2 with ei | _
    · wp_auto
      wp_apply wp_map_lookup1 $$ HBM as -
      simp only [HBMp, Option.getD_some]
      wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlk Hown Hback]
      · iapply Hback; iunfold wSlot; iexists wi, cid, Ew, sent2, pend2, GoInterface.ok ei
        iframe Hown; ileft; ipureintro; simp
      wp_end
    have H2 : sent2 ++ pend2 = ansStream k (L ++ [(Batch.mk x (clientName cl) [r])]) := by
      rw [Hk2.2.2.1, (Hk2.2.2.2.2.1 rfl), List.take_length, H1, HL.1, ansStream_snoc]
    wp_auto
    wp_apply EtcdGrove.bufio.Writer.Flush.wp_proof w wi _ _ Ew 4096 sent2 pend2 GoInterface.nil
      $$ Hown as %e3 ⟨%k3, %Hf3, Hown⟩
    have H3 : sent2 ++ pend2.take k3 ++ pend2.drop k3 =
        ansStream k (L ++ [(Batch.mk x (clientName cl) [r])]) := by
      rw [List.append_assoc, List.take_append_drop, H2]
    rcases e3 with ei | _ <;> wp_auto <;>
      wp_apply wp_map_lookup1 $$ HBM as - <;> simp only [HBMp, Option.getD_some] <;>
      wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlk Hown Hback] <;>
      first
      | (iapply Hback; iunfold wSlot; iexists wi, cid, Ew, _, _, _
         iframe Hown; iright; iexists L ++ [(Batch.mk x (clientName cl) [r])]
         isplitr
         · ipureintro
           exact ⟨H3, HL'⟩
         iexact HLs')
      | wp_end

theorem startOutgoingLinks_proof : startOutgoingLinks.spec (GF := GF) (hG := hG) := by
  intro γ c k pr
  wp_start as #Hsh
  ihave ⟨-, -, #Hch, -, -⟩ := proxyShared_net $$ Hsh
  iunfold sharedChans at Hch
  icases Hch with ⟨#Ho, -⟩
  iunfold chanField at Ho
  icases Ho with ⟨%och, %γo, #Hoch, #Hbag⟩
  wp_auto
  ipersist pr
  ihave HI : (∃ i : w64, "i" ∷ i_ptr ↦ i : IProp GF) $$ [i]
  · iexists _; iframe
  wp_for HI
  wp_if_destruct
  · wp_apply wp_fork $$ []
    · wp_auto
      wp_for
      wp_apply wp_bag_receive $$ [$Hbag] as %v Hv
      iunfold outP at Hv
      icases Hv with ⟨%rp, %l, %cl, %x, %r, #Hrp, %Hok, #Hrep, #Hans⟩
      wp_auto
      wp_apply internalSendMessage_proof γ c k pr v.Peer' rp l cl x r $$ [$Hsh $Hrep $Hans]
      · ipureintro; exact ⟨Hok.1, Hok.2.1⟩
      wp_for_post
      iframe
    wp_for_post
    iframe
    iexists _; iframe
  · wp_end

end proofs

end Perennial.raxos

/-
(Ported from dsverify-lab `examples/rabia/proof/Proof/rabia/roles/server/layers/proxy/KVSExecutor.lean`, run `rabia-r1wake-1`.)

`(*Proxy).KVSExecutor`: executes the decided slots in order. Loop invariant: `CurrSeq = seq`, the
store is the commands `cmds` of the slots before `seq` executed (`prefixFacts seq cmds`). Each
round reads slot `seq`'s decision through its invariant (`slotsInv`, `GetDecisionOrWake`'s atomic
update; its `decInfo` when done: the decision's facts and the facts of the slots before, whose
commands are `cmds` by `prefixFacts_agree`), executes its batch in order and replies to each
request (`singleExecuteAndReply`). R1-wake: when the slot is not done, the round waits in a
blocking select on `Done` (a bag of `False`: never fires) and the slot's wake channel (a broadcast
channel carrying `True`); the wakeup gives nothing, and the loop goes on with its invariant as it
was, rereading the slot.
`Done` is never closed or sent on: the loop never ends.
-/
module

public import Dsverify.Proof.rabia.roles.server.layers.proxy.singleExecuteAndReply
public import Dsverify.Proof.rabia.internal.ledger.Slot__GetDecisionOrWake
public import Dsverify.Proof.github_com.rs.zerolog.Spec
public import Dsverify.Proof.rabia.internal.tcp.ProxyTCP__ClientSendChan

@[expose] public section

noncomputable section

namespace Perennial.rabia.roles.server.layers.proxy

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode model Net rabia.internal.message
  rabia.internal.config rabia.internal.tcp rabia.roles.server.layers.consensus rabia
  rabia.internal.ledger

set_option linter.unusedSectionVars false

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics] [π : NetProtoGS]
variable [package_sem : rabia.roles.server.layers.proxy.Assumptions] [github_com.rs.zerolog.Hyps GF]

/-- The decision of slot `s` read through its invariant (`GetDecisionOrWake`'s atomic update,
the invariant opened around its commit): when done, its facts (`decInfo`); when not, a wake
channel (a broadcast channel carrying `True`). Unfolds consensus's `slotsInv`/`slotInv` (instead
of the law `readDecision`, whose credit cannot be given back by the atomic update's abort). -/
theorem wp_GetDecisionOrWake_slot (γ : Names) (cf : RCfg) (k : Nat) (γl : SrvNames) (γc : ConsNames) (s : Nat)
    (e : SlotV) (he : γl.slots[s]? = some e) :
    ⊢ ∀ Φ : val → IProp GF, isPkgInit (PROP := IProp GF) pkg_id.rabia.internal.ledger -∗
      isSlot e.loc e.γ e.q -∗ slotsInv γ cf k γl γc -∗
      (∀ (v : ConsensusObj) (b : Bool) (w : GoChan),
        (if b then ∃ st : SlotSt, ⌜st.isDone = true⌝ ∗ objRep v st.decision ∗ decInfo γ cf s st
         else ∃ γw : ChanNames, ownBroadcastChan w γw iprop(True) .Unknown) -∗
        Φ (PairV (PairV #v #b) #w)) -∗
    WP (App (Val (e.loc @!! go.GoType.PointerType Slot.ty @!! go!"GetDecisionOrWake")) (Val #())) {{ Φ }} := by
  iintro %Φ #Hpkg #Hisl #Hslots HΦ
  ihave Hspec := Slot.GetDecisionOrWake.wp_proof e.loc e.γ e.q $$ Hpkg Hisl
  iunfold atomic_wp at Hspec
  iapply Hspec
  iauintro
  unfold atomic_acc
  unfold slotsInv
  ihave #Hinv := BigSepL.bigSepL_lookup he $$ Hslots
  iinv Hinv with Hi Hclose
  unfold consensus.slotInv
  icases Hi with ⟨%st, Hst, Hdi, Hg⟩
  imod Hst
  imod Hdi with #Hdi
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  iexists (⟨st, ⟨⟩⟩ : (Tele.cons fun _ : SlotSt => Tele.nil).Arg)
  dsimp only [Tele.lam, Tele.app, Tele.bind, BI.tforall_cons, BI.tforall_nil, BIBase.wandM]
  iframe Hst
  isplit
  · iintro Hst
    imod Hmask with -
    imod Hclose $$ [Hst Hg] with -
    · inext
      iexists st
      iframe Hst Hg Hdi
    imodintro
    iframe
  · iintro Hst
    imod Hmask with -
    imod Hclose $$ [Hst Hg] with -
    · inext
      iexists st
      iframe Hst Hg Hdi
    imodintro
    cases hd : st.isDone
    · simp only [Bool.false_eq_true, ↓reduceIte]
      iintro %x %w Hx
      iapply HΦ
      simp only [Bool.false_eq_true, ↓reduceIte]
      iexact Hx
    · simp only [↓reduceIte]
      iintro %x %w Hx
      iapply HΦ
      simp only [↓reduceIte]
      iexists st
      iframe Hx Hdi
      ipureintro; exact hd

theorem Proxy.KVSExecutor.wp_of
    (hCSC : ProxyTCP.ClientSendChan.spec (GF := GF)) :
    Proxy.KVSExecutor.spec (GF := GF) := by
  have hDebug := github_com.rs.zerolog.Logger.Debug.wp_proof (GF := GF)
  have hUint32 := github_com.rs.zerolog.Event.Uint32.wp_proof (GF := GF)
  have hBool := github_com.rs.zerolog.Event.Bool.wp_proof (GF := GF)
  have hMsg := github_com.rs.zerolog.Event.Msg.wp_proof (GF := GF)
  intro γ cf k γl γc p
  wp_start as ⟨#Hconf, #Hsh, #Hcfg, Hres⟩
  wp_apply wp_with_defer as %dfr Hdfr
  unfold proxyKvsRes
  icases Hres with ⟨%ch, %wg, %t, %kv, %ledger, %cd, #Hf, Hseq, Hcd, Hkv, #Hdone, #Hled, #Hslots, #Htcp⟩
  unfold proxyFields
  icases Hf with ⟨%id, %hid, #HSvrId, #HWg, #HDone, #HCin, #HToNet, #HNetIn, #HTCP, #HKV, #HExec,
    #HExecR, #HLedger⟩
  icases confRO_val $$ Hconf with ⟨%ps, #Hc⟩
  iStructNamed Hc
  unfold ledgerRO
  icases Hled with ⟨#Hls, %Hlen, #Hslotl⟩
  ihave %Hlsl := ownSlice_len _ _ _ $$ Hls
  have hledlen : sint.Z ledger.len = 10000 := by
    obtain ⟨h1, h2⟩ := Hlsl; simp only [List.length_map, Hlen, lenLedger] at h1; word
  wp_auto
  ihave IH : iprop(∃ (seq : w32) (cmds : List GoString) (m : GMap GoString GoString) (cd : Loc),
      "Hseq" ∷ structFieldRef Proxy go!"CurrSeq" p ↦ seq ∗
      "Hcd" ∷ structFieldRef Proxy go!"CurrDec" p ↦ cd ∗
      "Hkv" ∷ ownMap kv (DFrac.own 1) m ∗ "%Hrel" ∷ ⌜StoreRel m (stateOfCmds cmds)⌝ ∗
      "#Hpf" ∷ prefixFacts γ.rab seq.toNat cmds ∗ "%Hseqb" ∷ ⌜seq.toNat ≤ lenLedger⌝)
      $$ [Hseq Hcd Hkv]
  · iexists (W32 0), [], ∅, cd
    iframe
    isplitr
    · ipureintro; exact storeRel_empty
    rw [show (W32 0).toNat = 0 from rfl]
    simp only [prefixFacts]
    ipureintro; exact ⟨trivial, by decide⟩
  wp_for IH
  iapply chan.wp_select_nonblocking
  isplit
  · iapply BigAndL.bigAndL_singleton.2
    simp only [chan.nonblockingClausePre]
    iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, ch.done, γl.done
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply is_bag_is_chan $$ Hdone
    unfold nonblockingRecvAu
    isplit
    · iapply bag_false_nonblocking_recv_au γl.done ch.done doneP (fun _ => .rfl) $$ Hdone
    · itrivial
  wp_auto
  have hmod : (seq % W32 10000).toNat = seq.toNat % 10000 := by
    rw [BitVec.toNat_umod]; rfl
  have hsl : seq.toNat % 10000 < lenLedger := by simp only [lenLedger]; omega
  obtain ⟨e, he⟩ : ∃ e, γl.slots[seq.toNat % 10000]? = some e :=
    ⟨_, List.getElem?_eq_getElem (by rw [Hlen]; exact hsl)⟩
  ihave #Hisl := BigSepL.bigSepL_lookup he $$ Hslotl
  ihave ⟨#Hq, #Hterm⟩ := isSlot_queue $$ Hisl
  have hidx : sint.Z (W64 (uint.Z (seq % W32 10000))) = ((seq.toNat % 10000 : Nat) : Int) := by
    rw [← hmod]; word
  rw [ite_eq_left (by rw [hidx, hledlen]; simp only [lenLedger] at hsl; omega)]
  wp_apply wp_load_slice_index _ _ _ _ e.loc (by rw [hidx]; omega) $$ [$Hls] as -
  · ipureintro; rw [hidx, Int.toNat_natCast, List.getElem?_map, he]; rfl
  wp_if_destruct
  · -- `seq < LenLedger`: slot `seq`
    have hlt : seq.toNat < 10000 := by
      have : (seq / W32 10000).toNat = 0 := by rw [Hif]; rfl
      rw [BitVec.toNat_udiv] at this
      simp only [lenLedger] at Hseqb
      have h2 : (W32 10000).toNat = 10000 := rfl
      rw [h2] at this
      omega
    have hsi : seq.toNat % 10000 = seq.toNat := Nat.mod_eq_of_lt hlt
    rw [ite_eq_left (by rw [hidx, hledlen]; simp only [lenLedger] at hsl; omega)]
    wp_apply wp_load_slice_index _ _ _ _ e.loc (by rw [hidx]; omega) $$ [$Hls] as -
    · ipureintro; rw [hidx, Int.toNat_natCast, List.getElem?_map, he]; rfl
    rw [hsi] at he
    wp_apply wp_GetDecisionOrWake_slot γ cf k γl γc seq.toNat e he $$ [] Hisl Hslots as %v %b %w Hb
    cases b with
    | true =>
      simp only [Bool.not_true, ↓reduceIte]
      wp_auto
      icases Hb with ⟨%st, %hdone, #Hrep, #Hdi⟩
      unfold decInfo
      simp only [hdone, ↓reduceIte]
      icases Hdi with ⟨%d, %cmds', #Hdec, #Hdobj, #Hpf'⟩
      ihave %hcm := prefixFacts_agree γ.rab seq.toNat cmds' cmds $$ [$Hpf' $Hpf]
      subst cmds'
      ihave %hv := objRep_fields $$ Hrep
      have hs1 : (seq + W32 1).toNat = seq.toNat + 1 := by
        rw [BitVec.toNat_add]; simp only [show (W32 1).toNat = 1 from rfl]; omega
      cases d with
      | null =>
        unfold decObjOk
        icases Hdobj with %hnull
        rw [hv.2.2.2, hnull.1]
        wp_auto
        wp_apply hDebug as %ev -
        wp_apply hUint32
        wp_apply hBool
        wp_apply hMsg
        wp_for_post
        iframe
        iexists seq + W32 1, cmds, m, dec_ptr
        iframe
        rw [hs1]
        isplitr
        · ipureintro; exact Hrel
        isplitr
        · simp only [prefixFacts]
          iexists cmds, .null
          iframe Hpf Hdec
          ipureintro; rfl
        ipureintro; simp only [lenLedger]; omega
      | obj id =>
        unfold decObjOk
        icases Hdobj with ⟨%hid, #Hok⟩
        unfold objOk
        icases Hok with ⟨%rs, #Hpo, #Hrg, %hok⟩
        obtain ⟨hnull, hcids, hcseqs, -, -, hrs, hpid, hcmds⟩ := hok
        have hlen : ∀ cmd ∈ st.decision.commands, 1 + keyLen ≤ cmd.length := by
          intro cmd hcmd
          obtain ⟨i, hci, hi, -⟩ := hcmds cmd hcmd
          rw [hci]; exact cmdOf_length hi
        rw [hv.2.2.2, hnull]
        wp_auto
        wp_apply hDebug as %ev -
        wp_apply hUint32
        wp_apply hBool
        wp_apply hUint32
        wp_apply hUint32
        wp_apply hMsg
        wp_apply Proxy.wp_singleExecuteAndReply hCSC γ cf k p t kv m cmds dec_ptr v st.decision
          seq.toNat id rs st.decision.commands ⟨hcids, hcseqs, rfl⟩ hrs hlen $$ [$Hcd $dec $Hkv]
          as %m2 ⟨Hcd, Hdecp, Hkv, %Hrel2⟩
        · iframe Hconf HTCP HKV HExec Htcp Hrep
          isplitr
          · ipureintro; exact Hrel
          unfold replyFacts
          rw [← hid.1]
          iframe Hdec Hpo Hrg Hpf
        wp_for_post
        iframe
        iexists seq + W32 1, cmds ++ st.decision.commands, m2, dec_ptr
        iframe
        rw [hs1]
        isplitr
        · ipureintro; exact Hrel2
        isplitr
        · simp only [prefixFacts]
          iexists cmds, .obj id
          iframe Hpf Hdec
          iexists rs, st.decision.commands
          rw [← hid.1]
          iframe Hpo Hrg
          ipureintro; rfl
        ipureintro; simp only [lenLedger]; omega
    | false =>
      -- R1-wake: wait on `Done` and the slot's wake channel; the wakeup carries nothing
      simp only [Bool.not_false, Bool.false_eq_true, ↓reduceIte]
      icases Hb with ⟨%γw, #Hwk⟩
      wp_auto_lc 2
      wp_apply_core chan.wp_select_blocking
      iapply BigAndL.bigAndL_cons.2
      isplit
      · dsimp only [chan.blockingClausePre]
        iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, ch.done, γl.done
        isplitr
        · ipureintro; rfl
        isplitr
        · iapply is_bag_is_chan $$ Hdone
        iapply bag_false_recv_au γl.done ch.done doneP (fun _ => .rfl) $$ [$Hlc1 $Hlc2] Hdone
      iapply BigAndL.bigAndL_cons.2
      isplit
      · dsimp only [chan.blockingClausePre]
        iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, w, γw
        isplitr
        · ipureintro; rfl
        isplitr
        · iapply ownBroadcastChan_is_chan $$ Hwk
        iapply broadcast_chan_receive $$ Hwk
        iintro -
        wp_auto
        wp_for_post
        iframe
        iexists seq, cmds, m, cd
        iframe
        iframe Hpf
        ipureintro; exact ⟨Hrel, Hseqb⟩
      iapply BigAndL.bigAndL_nil.2
      itrivial
  · wp_for_post
    iframe
    iexists seq, cmds, m, cd
    iframe
    iframe Hpf
    ipureintro; exact ⟨Hrel, Hseqb⟩

/-- `Proxy.KVSExecutor.spec`: from tcp's `ClientSendChan`. -/
theorem Proxy.KVSExecutor.wp_proof : Proxy.KVSExecutor.spec (GF := GF) :=
  Proxy.KVSExecutor.wp_of ProxyTCP.ClientSendChan.wp_proof

end proof
end Perennial.rabia.roles.server.layers.proxy

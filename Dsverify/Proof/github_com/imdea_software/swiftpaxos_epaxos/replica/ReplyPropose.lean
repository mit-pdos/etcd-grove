/-
`ReplyProposeTS`: the one reply to a client connection, under `r.M`, on its registered writer
(the reply token is stored in the writer's slot: one reply per connection).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Interface.LibDeps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.replica.SendMsg

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net github_com.imdea_software.swiftpaxos_epaxos.kvs model

attribute [local instance] GooseGlobalGS.gooseInvGS

section heap
variable [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [go.Semantics]
variable [epaxos.Assumptions] [HasExt netExt] [π : NetProtoGS]
variable [EpBufioDeps GF]

theorem replica.Replica.ReplyProposeTS.spec_holds
    (hM : replica.defs.ProposeReplyTS.Marshal.spec (GF := GF)) : replica.Replica.ReplyProposeTS.spec (GF := GF) := by
  intro γ r id L p Rext reply w mu cid o v vsl ts dq dq'
  wp_start as ⟨%Hv, #Hfw, Hrep, Hvsl, #Hcw, Hrt, #Hfired⟩
  ihave #Hfw' := isReplicaFw_def $$ Hfw
  iunfold isReplicaFwDef at Hfw'
  icases Hfw' with ⟨#Hro, #Hfz, #Hmu, #Hph1, #Hph2⟩
  ihave #Hro' := fwRO_def $$ Hro
  iunfold fwRODef at Hro'
  icases Hro' with ⟨#HLog, #HLogv, #HN, -, #HId, -, -, -, #HPeers, #HReaders, #HWriters, -, -, -, -,
    #HAlive, -, #HRPC, -, -, -, #HShut, -, -, -, -, -, -, #HEwma, #HLat, #HDt, %HL, #HLf,
    #HCI, -, -⟩
  unfold fwMethod
  wp_method_call
  wp_call
  wp_auto
  wp_apply wp_with_defer as %defer Hdefer
  wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, HR⟩
  iunfold fwLockInv at HR
  icases HR with ⟨Hcore, HRext⟩
  rw [fwCore_unseal]
  iunfold fwCoreDef at Hcore
  icases Hcore with ⟨%ns, %CWm, %CW, %RT, %sm, #Hn, #Hi1, #Hi2, Hp, Hr, Hcwm, HCW, HRT, %HCR, Hcs, Hsm⟩
  rw [clientWriter_unseal] at *
  rw [replyTok_unseal] at *
  unfold clientWriterDef replyTokDef
  ihave %Hlk := ghost_map_lookup $$ HCW Hcw
  icases (BigSepM.bigSepM_lookup_acc (show get? CW w = some cid from Hlk)).1 $$ Hcs with ⟨Hs, Hcs⟩
  unfold clientSlotX
  icases Hs with ⟨%c, %sent, %pend, %err, %tc, %la, %ra, %ed, %eof, #Hci, Hw, Hst, %cl, %i, #Hrole⟩
  icases Hst with (%Hst | Hrt')
  rotate_left
  · iexfalso
    icases ghostMapElem_ne _ w w _ () () $$ Hrt Hrt' with %Hne
    exact absurd rfl Hne
  rw [show interface.mkOk (go.GoType.PointerType bufio.Writer.ty) #w = bwIface w from rfl]
  wp_apply (hM reply dq dq' ⟨okTRUE, W32 0, v, ts⟩ vsl w
      (connWr tc cid true la ra ed (repAccP γ (L.getD id [])) (repAccP_ppc γ _) 4096) sent pend err)
    $$ [Hw Hrep Hvsl] as ⟨⟨Hrep, Hvsl⟩, %sent2, %pend2, %e2, %Hw2, Hw⟩
  · simp only [connWr]
    iframe Hw Hrep Hvsl
    iintro %He
    rw [Hst]
    imodintro
    unfold repAccP
    iright
    iexists _
    iframe Hrole
    simp only
    unfold clientReplyOk
    iexists o, v, ts
    iframe Hfired
    ipureintro
    refine ⟨Hv.1, Hv.2, ?_⟩
    simp [ProposeReplyV.enc]
  wp_apply EpBufioDeps.flush w _ _ _ _ _ sent2 pend2 e2
    $$ [$Hw] as %e3 ⟨%k, %Hk3, Hw⟩
  ihave Hcs := Hcs $$ [Hw Hrt]
  · iexists c, sent2 ++ pend2.take k, pend2.drop k, e3, tc, la, ra, ed, eof
    simp only [wrOwn, connWr]
    iframe Hci Hw
    isplitl [Hrt]
    · iright; iexact Hrt
    iexists cl, i; iexact Hrole
  wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hcwm HCW HRT Hcs Hsm Hp Hr HRext]
  · unfold fwLockInv
    rw [fwCore_unseal]
    unfold fwCoreDef
    iframe
    inext
    iframe; iframe #
    ipureintro; exact HCR
  iapply HΦ
  iframe

end heap

end Perennial.github_com.imdea_software.swiftpaxos_epaxos

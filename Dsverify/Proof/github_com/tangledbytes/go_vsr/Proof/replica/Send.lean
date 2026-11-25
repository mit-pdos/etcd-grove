/-
Ported from dsverify-lab examples/vr/proof/VsrProof/Proof/replica/Send.lean (lab master 915f964;
notes/dsv-vr.md): over any `GF`, on the net extension; the hypotheses `H : replica.Hyps`
(`Hyps.lean`) for the `log/slog` methods and the `network`/`events` calls.
-/
/-
The replica's sends: each `sendX` method (a `Network.Send` with a closure that builds the event
from the replica's fields and writes it), for a valid message (its fact).
-/
module

public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Spec.replica
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.replica.Hyps
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.replica.Pure
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.replica.Ghost

@[expose] public section

noncomputable section

namespace Perennial.github_com.tangledbytes.go_vsr.pkg

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net VsrModel


section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [package_sem : replica.Assumptions] [net.FieldAssumptions] [π : NetProtoGS]
variable [encoding.json.DecoderRep GF]

/-- What a send needs of the replica `v` (persistent): its network is the `*TCP` `tcp`, the
addresses' protocols, the JSON codec, the system's invariant. -/
def replica.sendCtx (γ : VsrGhost.Names) (tcp : Loc) (v : replica.Replica)
    (C : models_lab.jsoncodec.JsonCodec GF) (F : List w8 → Bool → w64 × w64) : IProp GF :=
  iprop(∃ (me : GoString),
    ⌜v.network' = interface.mkOk (go.GoType.PointerType network.TCP.ty) #tcp⌝ ∗
    network.isTCP tcp γ me ∗ network.netProtos γ ∗ encoding.json.codecSet (GF := GF) ∗
    encoding.json.kitCodecOk (jc := C) F ∗ VsrGhost.sysInv γ)

instance replica.sendCtx_persistent (γ : VsrGhost.Names) (tcp : Loc) (v : replica.Replica)
    (C : models_lab.jsoncodec.JsonCodec GF) (F : List w8 → Bool → w64 × w64) :
    Persistent (replica.sendCtx γ tcp v C F) := by
  unfold replica.sendCtx; infer_instance

end defs

/-- A sent message's numbers fit in `uint64`: they are Go `uint64`s (and a log's entries' ids,
`Hlb`; a DoViewChange's log length is its `OpNum`). -/
macro "msg_bound" : tactic => `(tactic| (
  simp only [MsgBound, EntryBound]
  repeat' apply And.intro
  all_goals first | word | (intro e he; exact Hlb e he) | (rw [← hlen]; word)))

section proofs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [package_sem : replica.Assumptions] [net.FieldAssumptions] [π : NetProtoGS]
variable [encoding.json.DecoderRep GF]

set_option goose.wp.extras true

theorem replica.wp_sendStartViewChange (H : replica.Hyps (GF := GF) (hG := hG)) (rp : Loc) (v : replica.Replica)
    (γ : VsrGhost.Names) (tcp : Loc) (C : models_lab.jsoncodec.JsonCodec GF)
    (F : List w8 → Bool → w64 × w64) (a : ipv4port.IPv4Port) (vn : w64) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.tangledbytes.go_vsr.pkg.replica ∗
        rp ↦ v ∗ replica.sendCtx γ tcp v C F ∗ network.tcpSender tcp ∗ network.addrOk tcp a ∗
        VsrGhost.fact γ (.msg (.startViewChange (uint.nat vn) (uint.nat v.state'.ID'))) }}
      (App (App (Val (rp @!! go.GoType.PointerType replica.Replica.ty @!! go!"sendStartViewChange")) (Val #a)) (Val #vn))
    {{ (err : GoInterface), RET #err; rp ↦ v ∗ network.tcpSender tcp ∗ bufio.errOrNil err }} := by
  wp_start as ⟨Hr, #Hctx, Hsnd, #Ha, #Hf⟩
  wp_auto
  wp_pures
  wp_func_lits
  unfold replica.sendCtx
  icases Hctx with ⟨%me, %Hnet, #HisTCP, #Hprotos, #Hcodec, #Hkit, #Hsys⟩
  rw [Hnet]
  wp_auto
  have hb : MsgBound (.startViewChange (uint.nat vn) (uint.nat v.state'.ID')) := by msg_bound
  imod VsrReplica.fact_send' γ _ hb $$ Hsys Hf with %Hpl
  obtain ⟨Hplain, Hline⟩ := Hpl
  wp_apply (H.wp_TCP_Send (jc := C) tcp γ me a _ (iprop(r_ptr ↦ rp ∗ viewNum_ptr ↦ vn ∗ rp ↦ v))
    (iprop(r_ptr ↦ rp ∗ viewNum_ptr ↦ vn ∗ rp ↦ v))) $$ [Hsnd r viewNum Hr] as %err ⟨Hsnd, HRQ⟩
  · iframe HisTCP Ha Hprotos Hsnd r viewNum Hr
    unfold network.sendFn
    iintro %w %Φ' Hw ⟨r, viewNum, Hr⟩ HΦ'
    wp_auto
    ipersist ev
    wp_apply (H.wp_ToWriter (jc := C) F γ ev_ptr (.startViewChange (uint.nat vn) (uint.nat v.state'.ID')) w) $$ [Hw] as %err ⟨Hw, #Herr⟩
    · iframe Hcodec Hkit Hf Hw
      isplitl []
      · unfold events.isEvent
        simp only [events.typeOf, events.payloadOf]
        iexists _
        iframe ev
        iexists _
        ipureintro
        refine ⟨rfl, ?_⟩
        simp
      · ipureintro; exact ⟨Hplain, hb, Hline⟩
    iapply HΦ' $$ Hw Herr
    iframe
  icases HRQ with ⟨#Herr, HRQ⟩
  icases HRQ with (⟨r, viewNum, Hr⟩ | ⟨%_, r, viewNum, Hr⟩) <;> wp_end <;> iframe Hr Hsnd Herr

theorem replica.wp_sendPrepareOKToPrimary (H : replica.Hyps (GF := GF) (hG := hG)) (rp : Loc) (v : replica.Replica)
    (γ : VsrGhost.Names) (tcp : Loc) (C : models_lab.jsoncodec.JsonCodec GF)
    (F : List w8 → Bool → w64 × w64) (a : ipv4port.IPv4Port) (k : w64) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.tangledbytes.go_vsr.pkg.replica ∗
        rp ↦ v ∗ replica.sendCtx γ tcp v C F ∗ network.tcpSender tcp ∗ network.addrOk tcp a ∗
        VsrGhost.fact γ (.msg (.prepareOK (uint.nat v.state'.ViewNumber') (uint.nat k) (uint.nat v.state'.ID'))) }}
      (App (App (Val (rp @!! go.GoType.PointerType replica.Replica.ty @!! go!"sendPrepareOKToPrimary")) (Val #a)) (Val #k))
    {{ (err : GoInterface), RET #err; rp ↦ v ∗ network.tcpSender tcp ∗ bufio.errOrNil err }} := by
  wp_start as ⟨Hr, #Hctx, Hsnd, #Ha, #Hf⟩
  wp_auto
  wp_pures
  wp_func_lits
  unfold replica.sendCtx
  icases Hctx with ⟨%me, %Hnet, #HisTCP, #Hprotos, #Hcodec, #Hkit, #Hsys⟩
  rw [Hnet]
  wp_auto
  have hb : MsgBound (.prepareOK (uint.nat v.state'.ViewNumber') (uint.nat k) (uint.nat v.state'.ID')) := by msg_bound
  imod VsrReplica.fact_send' γ _ hb $$ Hsys Hf with %Hpl
  obtain ⟨Hplain, Hline⟩ := Hpl
  wp_apply (H.wp_TCP_Send (jc := C) tcp γ me a _ (iprop(r_ptr ↦ rp ∗ opnum_ptr ↦ k ∗ rp ↦ v))
    (iprop(r_ptr ↦ rp ∗ opnum_ptr ↦ k ∗ rp ↦ v))) $$ [Hsnd r opnum Hr] as %err ⟨Hsnd, HRQ⟩
  · iframe HisTCP Ha Hprotos Hsnd r opnum Hr
    unfold network.sendFn
    iintro %w %Φ' Hw ⟨r, opnum, Hr⟩ HΦ'
    wp_auto
    ipersist ev
    wp_apply (H.wp_ToWriter (jc := C) F γ ev_ptr (.prepareOK (uint.nat v.state'.ViewNumber') (uint.nat k) (uint.nat v.state'.ID')) w) $$ [Hw] as %err ⟨Hw, #Herr⟩
    · iframe Hcodec Hkit Hf Hw
      isplitl []
      · unfold events.isEvent
        simp only [events.typeOf, events.payloadOf]
        iexists _
        iframe ev
        iexists _
        ipureintro
        refine ⟨rfl, ?_⟩
        simp
      · ipureintro; exact ⟨Hplain, hb, Hline⟩
    iapply HΦ' $$ Hw Herr
    iframe
  icases HRQ with ⟨#Herr, HRQ⟩
  icases HRQ with (⟨r, opnum, Hr⟩ | ⟨%_, r, opnum, Hr⟩) <;> wp_end <;> iframe Hr Hsnd Herr

theorem replica.wp_sendCommitToBackup (H : replica.Hyps (GF := GF) (hG := hG)) (rp : Loc) (v : replica.Replica)
    (γ : VsrGhost.Names) (tcp : Loc) (C : models_lab.jsoncodec.JsonCodec GF)
    (F : List w8 → Bool → w64 × w64) (a : ipv4port.IPv4Port) (c : w64) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.tangledbytes.go_vsr.pkg.replica ∗
        rp ↦ v ∗ replica.sendCtx γ tcp v C F ∗ network.tcpSender tcp ∗ network.addrOk tcp a ∗
        VsrGhost.fact γ (.msg (.commit (uint.nat v.state'.ViewNumber') (uint.nat c) (uint.nat v.state'.ID'))) }}
      (App (App (Val (rp @!! go.GoType.PointerType replica.Replica.ty @!! go!"sendCommitToBackup")) (Val #a)) (Val #c))
    {{ (err : GoInterface), RET #err; rp ↦ v ∗ network.tcpSender tcp ∗ bufio.errOrNil err }} := by
  wp_start as ⟨Hr, #Hctx, Hsnd, #Ha, #Hf⟩
  wp_auto
  wp_pures
  wp_func_lits
  unfold replica.sendCtx
  icases Hctx with ⟨%me, %Hnet, #HisTCP, #Hprotos, #Hcodec, #Hkit, #Hsys⟩
  rw [Hnet]
  wp_auto
  have hb : MsgBound (.commit (uint.nat v.state'.ViewNumber') (uint.nat c) (uint.nat v.state'.ID')) := by msg_bound
  imod VsrReplica.fact_send' γ _ hb $$ Hsys Hf with %Hpl
  obtain ⟨Hplain, Hline⟩ := Hpl
  wp_apply (H.wp_TCP_Send (jc := C) tcp γ me a _ (iprop(r_ptr ↦ rp ∗ commitnum_ptr ↦ c ∗ rp ↦ v))
    (iprop(r_ptr ↦ rp ∗ commitnum_ptr ↦ c ∗ rp ↦ v))) $$ [Hsnd r commitnum Hr] as %err ⟨Hsnd, HRQ⟩
  · iframe HisTCP Ha Hprotos Hsnd r commitnum Hr
    unfold network.sendFn
    iintro %w %Φ' Hw ⟨r, commitnum, Hr⟩ HΦ'
    wp_auto
    ipersist ev
    wp_apply (H.wp_ToWriter (jc := C) F γ ev_ptr (.commit (uint.nat v.state'.ViewNumber') (uint.nat c) (uint.nat v.state'.ID')) w) $$ [Hw] as %err ⟨Hw, #Herr⟩
    · iframe Hcodec Hkit Hf Hw
      isplitl []
      · unfold events.isEvent
        simp only [events.typeOf, events.payloadOf]
        iexists _
        iframe ev
        iexists _
        ipureintro
        refine ⟨rfl, ?_⟩
        simp
      · ipureintro; exact ⟨Hplain, hb, Hline⟩
    iapply HΦ' $$ Hw Herr
    iframe
  icases HRQ with ⟨#Herr, HRQ⟩
  icases HRQ with (⟨r, commitnum, Hr⟩ | ⟨%_, r, commitnum, Hr⟩) <;> wp_end <;> iframe Hr Hsnd Herr

theorem replica.wp_sendGetStateToReplica (H : replica.Hyps (GF := GF) (hG := hG)) (rp : Loc) (v : replica.Replica)
    (γ : VsrGhost.Names) (tcp : Loc) (C : models_lab.jsoncodec.JsonCodec GF)
    (F : List w8 → Bool → w64 × w64) (a : ipv4port.IPv4Port) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.tangledbytes.go_vsr.pkg.replica ∗
        rp ↦ v ∗ replica.sendCtx γ tcp v C F ∗ network.tcpSender tcp ∗ network.addrOk tcp a ∗
        VsrGhost.fact γ (.msg (.getState (uint.nat v.state'.ViewNumber') (uint.nat v.state'.OpNum') (uint.nat v.state'.ID'))) }}
      (App (Val (rp @!! go.GoType.PointerType replica.Replica.ty @!! go!"sendGetStateToReplica")) (Val #a))
    {{ (err : GoInterface), RET #err; rp ↦ v ∗ network.tcpSender tcp ∗ bufio.errOrNil err }} := by
  wp_start as ⟨Hr, #Hctx, Hsnd, #Ha, #Hf⟩
  wp_auto
  wp_pures
  wp_func_lits
  unfold replica.sendCtx
  icases Hctx with ⟨%me, %Hnet, #HisTCP, #Hprotos, #Hcodec, #Hkit, #Hsys⟩
  rw [Hnet]
  wp_auto
  have hb : MsgBound (.getState (uint.nat v.state'.ViewNumber') (uint.nat v.state'.OpNum') (uint.nat v.state'.ID')) := by msg_bound
  imod VsrReplica.fact_send' γ _ hb $$ Hsys Hf with %Hpl
  obtain ⟨Hplain, Hline⟩ := Hpl
  wp_apply (H.wp_TCP_Send (jc := C) tcp γ me a _ (iprop(r_ptr ↦ rp ∗ rp ↦ v))
    (iprop(r_ptr ↦ rp ∗ rp ↦ v))) $$ [Hsnd r Hr] as %err ⟨Hsnd, HRQ⟩
  · iframe HisTCP Ha Hprotos Hsnd r Hr
    unfold network.sendFn
    iintro %w %Φ' Hw ⟨r, Hr⟩ HΦ'
    wp_auto
    ipersist ev
    wp_apply (H.wp_ToWriter (jc := C) F γ ev_ptr (.getState (uint.nat v.state'.ViewNumber') (uint.nat v.state'.OpNum') (uint.nat v.state'.ID')) w) $$ [Hw] as %err ⟨Hw, #Herr⟩
    · iframe Hcodec Hkit Hf Hw
      isplitl []
      · unfold events.isEvent
        simp only [events.typeOf, events.payloadOf]
        iexists _
        iframe ev
        iexists _
        ipureintro
        refine ⟨rfl, ?_⟩
        simp
      · ipureintro; exact ⟨Hplain, hb, Hline⟩
    iapply HΦ' $$ Hw Herr
    iframe
  icases HRQ with ⟨#Herr, HRQ⟩
  icases HRQ with (⟨r, Hr⟩ | ⟨%_, r, Hr⟩) <;> wp_end <;> iframe Hr Hsnd Herr

theorem replica.wp_sendReplyToClient (H : replica.Hyps (GF := GF) (hG := hG)) (rp : Loc) (v : replica.Replica)
    (γ : VsrGhost.Names) (tcp : Loc) (C : models_lab.jsoncodec.JsonCodec GF)
    (F : List w8 → Bool → w64 × w64) (a : ipv4port.IPv4Port) (cid rid : w64) (res : GoString) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.tangledbytes.go_vsr.pkg.replica ∗
        rp ↦ v ∗ replica.sendCtx γ tcp v C F ∗ network.tcpSender tcp ∗ network.addrOk tcp a ∗
        VsrGhost.fact γ (.msg (.reply (uint.nat rid) (uint.nat cid) (uint.nat v.state'.ViewNumber') res)) }}
      (App (App (App (App (Val (rp @!! go.GoType.PointerType replica.Replica.ty @!! go!"sendReplyToClient")) (Val #a)) (Val #cid)) (Val #rid)) (Val #res))
    {{ (err : GoInterface), RET #err; rp ↦ v ∗ network.tcpSender tcp ∗ bufio.errOrNil err }} := by
  wp_start as ⟨Hr, #Hctx, Hsnd, #Ha, #Hf⟩
  wp_auto
  wp_pures
  wp_func_lits
  unfold replica.sendCtx
  icases Hctx with ⟨%me, %Hnet, #HisTCP, #Hprotos, #Hcodec, #Hkit, #Hsys⟩
  rw [Hnet]
  wp_auto
  have hb : MsgBound (.reply (uint.nat rid) (uint.nat cid) (uint.nat v.state'.ViewNumber') res) := by msg_bound
  imod VsrReplica.fact_send' γ _ hb $$ Hsys Hf with %Hpl
  obtain ⟨Hplain, Hline⟩ := Hpl
  wp_apply (H.wp_TCP_Send (jc := C) tcp γ me a _ (iprop(r_ptr ↦ rp ∗ res_ptr ↦ res ∗ reqID_ptr ↦ rid ∗ clientID_ptr ↦ cid ∗ rp ↦ v))
    (iprop(r_ptr ↦ rp ∗ res_ptr ↦ res ∗ reqID_ptr ↦ rid ∗ clientID_ptr ↦ cid ∗ rp ↦ v))) $$ [Hsnd r res reqID clientID Hr] as %err ⟨Hsnd, HRQ⟩
  · iframe HisTCP Ha Hprotos Hsnd r res reqID clientID Hr
    unfold network.sendFn
    iintro %w %Φ' Hw ⟨r, res, reqID, clientID, Hr⟩ HΦ'
    wp_auto
    ipersist ev
    wp_apply (H.wp_ToWriter (jc := C) F γ ev_ptr (.reply (uint.nat rid) (uint.nat cid) (uint.nat v.state'.ViewNumber') res) w) $$ [Hw] as %err ⟨Hw, #Herr⟩
    · iframe Hcodec Hkit Hf Hw
      isplitl []
      · unfold events.isEvent
        simp only [events.typeOf, events.payloadOf]
        iexists _
        iframe ev
        iexists _
        ipureintro
        refine ⟨rfl, ?_⟩
        simp
      · ipureintro; exact ⟨Hplain, hb, Hline⟩
    iapply HΦ' $$ Hw Herr
    iframe
  icases HRQ with ⟨#Herr, HRQ⟩
  icases HRQ with (⟨r, res, reqID, clientID, Hr⟩ | ⟨%_, r, res, reqID, clientID, Hr⟩) <;> wp_end <;> iframe Hr Hsnd Herr

theorem replica.wp_sendPrepareToBackup (H : replica.Hyps (GF := GF) (hG := hG)) (rp : Loc) (v : replica.Replica)
    (γ : VsrGhost.Names) (tcp : Loc) (C : models_lab.jsoncodec.JsonCodec GF)
    (F : List w8 → Bool → w64 × w64) (a : ipv4port.IPv4Port) (req : events.Request) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.tangledbytes.go_vsr.pkg.replica ∗
        rp ↦ v ∗ replica.sendCtx γ tcp v C F ∗ network.tcpSender tcp ∗ network.addrOk tcp a ∗
        VsrGhost.fact γ (.msg (.prepare (uint.nat v.state'.ViewNumber') (uint.nat v.state'.OpNum') (uint.nat v.state'.CommitNumber') ⟨req.Op', uint.nat req.ClientID', uint.nat req.ID'⟩ (uint.nat v.state'.ID'))) }}
      (App (App (Val (rp @!! go.GoType.PointerType replica.Replica.ty @!! go!"sendPrepareToBackup")) (Val #a)) (Val #req))
    {{ (err : GoInterface), RET #err; rp ↦ v ∗ network.tcpSender tcp ∗ bufio.errOrNil err }} := by
  wp_start as ⟨Hr, #Hctx, Hsnd, #Ha, #Hf⟩
  wp_auto
  wp_pures
  wp_func_lits
  unfold replica.sendCtx
  icases Hctx with ⟨%me, %Hnet, #HisTCP, #Hprotos, #Hcodec, #Hkit, #Hsys⟩
  rw [Hnet]
  wp_auto
  have hb : MsgBound (.prepare (uint.nat v.state'.ViewNumber') (uint.nat v.state'.OpNum') (uint.nat v.state'.CommitNumber') ⟨req.Op', uint.nat req.ClientID', uint.nat req.ID'⟩ (uint.nat v.state'.ID')) := by msg_bound
  imod VsrReplica.fact_send' γ _ hb $$ Hsys Hf with %Hpl
  obtain ⟨Hplain, Hline⟩ := Hpl
  wp_apply (H.wp_TCP_Send (jc := C) tcp γ me a _ (iprop(r_ptr ↦ rp ∗ req_ptr ↦ req ∗ rp ↦ v))
    (iprop(r_ptr ↦ rp ∗ req_ptr ↦ req ∗ rp ↦ v))) $$ [Hsnd r req Hr] as %err ⟨Hsnd, HRQ⟩
  · iframe HisTCP Ha Hprotos Hsnd r req Hr
    unfold network.sendFn
    iintro %w %Φ' Hw ⟨r, req, Hr⟩ HΦ'
    wp_auto
    ipersist ev
    wp_apply (H.wp_ToWriter (jc := C) F γ ev_ptr (.prepare (uint.nat v.state'.ViewNumber') (uint.nat v.state'.OpNum') (uint.nat v.state'.CommitNumber') ⟨req.Op', uint.nat req.ClientID', uint.nat req.ID'⟩ (uint.nat v.state'.ID')) w) $$ [Hw] as %err ⟨Hw, #Herr⟩
    · iframe Hcodec Hkit Hf Hw
      isplitl []
      · unfold events.isEvent
        simp only [events.typeOf, events.payloadOf]
        iexists _
        iframe ev
        iexists _
        ipureintro
        refine ⟨rfl, ?_⟩
        simp [events.reqIs]
      · ipureintro; exact ⟨Hplain, hb, Hline⟩
    iapply HΦ' $$ Hw Herr
    iframe
  icases HRQ with ⟨#Herr, HRQ⟩
  icases HRQ with (⟨r, req, Hr⟩ | ⟨%_, r, req, Hr⟩) <;> wp_end <;> iframe Hr Hsnd Herr

theorem replica.wp_sendDoViewChangeToPrimary (H : replica.Hyps (GF := GF) (hG := hG)) (rp : Loc) (v : replica.Replica)
    (γ : VsrGhost.Names) (tcp : Loc) (C : models_lab.jsoncodec.JsonCodec GF)
    (F : List w8 → Bool → w64 × w64) (a : ipv4port.IPv4Port) (lg : List Entry) (hlen : uint.nat v.state'.OpNum' = lg.length) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.tangledbytes.go_vsr.pkg.replica ∗
        rp ↦ v ∗ replica.sendCtx γ tcp v C F ∗ network.tcpSender tcp ∗ network.addrOk tcp a ∗
        log.ownLogs v.state'.Logs' DFrac.discard lg ∗
        VsrGhost.fact γ (.msg (.doViewChange ⟨uint.nat v.state'.ViewNumber', lg, uint.nat v.internal'.lastStableViewNumber', uint.nat v.state'.CommitNumber', uint.nat v.state'.ID'⟩)) }}
      (App (Val (rp @!! go.GoType.PointerType replica.Replica.ty @!! go!"sendDoViewChangeToPrimary")) (Val #a))
    {{ (err : GoInterface), RET #err; rp ↦ v ∗ network.tcpSender tcp ∗ bufio.errOrNil err }} := by
  wp_start as ⟨Hr, #Hctx, Hsnd, #Ha, #Hlog, #Hf⟩
  ihave ⟨%Hlb, -⟩ := log.ownLogs_bound _ _ _ $$ Hlog
  wp_auto
  wp_pures
  wp_func_lits
  unfold replica.sendCtx
  icases Hctx with ⟨%me, %Hnet, #HisTCP, #Hprotos, #Hcodec, #Hkit, #Hsys⟩
  rw [Hnet]
  wp_auto
  have hb : MsgBound (.doViewChange ⟨uint.nat v.state'.ViewNumber', lg, uint.nat v.internal'.lastStableViewNumber', uint.nat v.state'.CommitNumber', uint.nat v.state'.ID'⟩) := by msg_bound
  imod VsrReplica.fact_send' γ _ hb $$ Hsys Hf with %Hpl
  obtain ⟨Hplain, Hline⟩ := Hpl
  wp_apply (H.wp_TCP_Send (jc := C) tcp γ me a _ (iprop(r_ptr ↦ rp ∗ rp ↦ v))
    (iprop(r_ptr ↦ rp ∗ rp ↦ v))) $$ [Hsnd r Hr] as %err ⟨Hsnd, HRQ⟩
  · iframe HisTCP Ha Hprotos Hsnd r Hr
    unfold network.sendFn
    iintro %w %Φ' Hw ⟨r, Hr⟩ HΦ'
    wp_auto
    ipersist ev
    wp_apply (H.wp_ToWriter (jc := C) F γ ev_ptr (.doViewChange ⟨uint.nat v.state'.ViewNumber', lg, uint.nat v.internal'.lastStableViewNumber', uint.nat v.state'.CommitNumber', uint.nat v.state'.ID'⟩) w) $$ [Hw] as %err ⟨Hw, #Herr⟩
    · iframe Hcodec Hkit Hf Hw
      isplitl []
      · unfold events.isEvent
        simp only [events.typeOf, events.payloadOf]
        iexists _
        iframe ev
        iexists _
        isplitl []
        · ipureintro
          refine ⟨rfl, ?_⟩
          simp [hlen]
        · iexact Hlog
      · ipureintro; exact ⟨Hplain, hb, Hline⟩
    iapply HΦ' $$ Hw Herr
    iframe
  icases HRQ with ⟨#Herr, HRQ⟩
  icases HRQ with (⟨r, Hr⟩ | ⟨%_, r, Hr⟩) <;> wp_end <;> iframe Hr Hsnd Herr

theorem replica.wp_sendStartViewToBackup (H : replica.Hyps (GF := GF) (hG := hG)) (rp : Loc) (v : replica.Replica)
    (γ : VsrGhost.Names) (tcp : Loc) (C : models_lab.jsoncodec.JsonCodec GF)
    (F : List w8 → Bool → w64 × w64) (a : ipv4port.IPv4Port) (lg : List Entry) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.tangledbytes.go_vsr.pkg.replica ∗
        rp ↦ v ∗ replica.sendCtx γ tcp v C F ∗ network.tcpSender tcp ∗ network.addrOk tcp a ∗
        log.ownLogs v.state'.Logs' DFrac.discard lg ∗
        VsrGhost.fact γ (.msg (.startView (uint.nat v.state'.ViewNumber') (uint.nat v.state'.OpNum') (uint.nat v.state'.CommitNumber') lg (uint.nat v.state'.ID'))) }}
      (App (Val (rp @!! go.GoType.PointerType replica.Replica.ty @!! go!"sendStartViewToBackup")) (Val #a))
    {{ (err : GoInterface), RET #err; rp ↦ v ∗ network.tcpSender tcp ∗ bufio.errOrNil err }} := by
  wp_start as ⟨Hr, #Hctx, Hsnd, #Ha, #Hlog, #Hf⟩
  ihave ⟨%Hlb, -⟩ := log.ownLogs_bound _ _ _ $$ Hlog
  wp_auto
  wp_pures
  wp_func_lits
  unfold replica.sendCtx
  icases Hctx with ⟨%me, %Hnet, #HisTCP, #Hprotos, #Hcodec, #Hkit, #Hsys⟩
  rw [Hnet]
  wp_auto
  have hb : MsgBound (.startView (uint.nat v.state'.ViewNumber') (uint.nat v.state'.OpNum') (uint.nat v.state'.CommitNumber') lg (uint.nat v.state'.ID')) := by msg_bound
  imod VsrReplica.fact_send' γ _ hb $$ Hsys Hf with %Hpl
  obtain ⟨Hplain, Hline⟩ := Hpl
  wp_apply (H.wp_TCP_Send (jc := C) tcp γ me a _ (iprop(r_ptr ↦ rp ∗ rp ↦ v))
    (iprop(r_ptr ↦ rp ∗ rp ↦ v))) $$ [Hsnd r Hr] as %err ⟨Hsnd, HRQ⟩
  · iframe HisTCP Ha Hprotos Hsnd r Hr
    unfold network.sendFn
    iintro %w %Φ' Hw ⟨r, Hr⟩ HΦ'
    wp_auto
    ipersist ev
    wp_apply (H.wp_ToWriter (jc := C) F γ ev_ptr (.startView (uint.nat v.state'.ViewNumber') (uint.nat v.state'.OpNum') (uint.nat v.state'.CommitNumber') lg (uint.nat v.state'.ID')) w) $$ [Hw] as %err ⟨Hw, #Herr⟩
    · iframe Hcodec Hkit Hf Hw
      isplitl []
      · unfold events.isEvent
        simp only [events.typeOf, events.payloadOf]
        iexists _
        iframe ev
        iexists _
        isplitl []
        · ipureintro
          refine ⟨rfl, ?_⟩
          simp
        · iexact Hlog
      · ipureintro; exact ⟨Hplain, hb, Hline⟩
    iapply HΦ' $$ Hw Herr
    iframe
  icases HRQ with ⟨#Herr, HRQ⟩
  icases HRQ with (⟨r, Hr⟩ | ⟨%_, r, Hr⟩) <;> wp_end <;> iframe Hr Hsnd Herr

end proofs

end Perennial.github_com.tangledbytes.go_vsr.pkg

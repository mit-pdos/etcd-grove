/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/rafthttp/logRaftCommunication.lean`
(PR etcd#21401).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.logRaftCommunication
public import Spec.go_uber_org.zap.Logger__Core
public import Spec.go_uber_org.zap.String
public import Spec.go_uber_org.zap.Uint64
public import Spec.go_uber_org.zap.Logger__Debug
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetType
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetTerm
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetIndex
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetCommit
public import Spec.go_etcd_io.raft.v3.raftpb.MessageType__String
public import Spec.go_etcd_io.etcd.client.pkg.v3.types.ID__String_ptr
public import Spec.encoding.binary.bigEndian__Uint64
public import Spec.google_golang_org.protobuf.proto.UnmarshalIRR

@[expose] public section

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.api go_etcd_io.raft.v3
open go_uber_org google_golang_org.protobuf go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Assumptions]

set_option hygiene false in
/-- The final `lg.Debug("Raft communication", ...)` call of `logRaftCommunication`. -/
local macro "debug_tail" : tactic => `(tactic| (
  (try wp_auto)
  wp_apply hZS as %f0 -
  (try wp_auto)
  wp_apply hGetType.1 m dq dqe cap ms $$ [Hmsg] as Hmsg
  · iframe # Hmsg
  (try wp_auto)
  wp_apply hMsgTypeStr as %mtStr -
  (try wp_auto)
  wp_apply hZS as %f1 -
  (try wp_auto)
  wp_apply hIDStr localID_ptr (DFrac.own 1) localID $$ [localID] as %locStr ⟨localID, -⟩
  · iframe # localID
  (try wp_auto)
  wp_apply hZS as %f2 -
  (try wp_auto)
  wp_apply hIDStr remote_ptr (DFrac.own 1) remote $$ [remote] as %remStr ⟨remote, -⟩
  · iframe # remote
  (try wp_auto)
  wp_apply hZS as %f3 -
  (try wp_auto)
  wp_apply hGetTerm.1 m dq dqe cap ms $$ [Hmsg] as Hmsg
  · iframe # Hmsg
  (try wp_auto)
  wp_apply hZU as %f4 -
  (try wp_auto)
  wp_apply hGetIndex.1 m dq dqe cap ms $$ [Hmsg] as Hmsg
  · iframe # Hmsg
  (try wp_auto)
  wp_apply hZU as %f5 -
  (try wp_auto)
  wp_apply hGetCommit.1 m dq dqe cap ms $$ [Hmsg] as Hmsg
  · iframe # Hmsg
  (try wp_auto)
  wp_apply hZU as %f6 -
  (try wp_auto)
  wp_apply hZU as %f7 -
  (try wp_auto)
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %fsl ⟨Hfsl, -⟩
  (try wp_auto)
  wp_apply hZDebug lg _ _ $$ []
  · iframe #; ipureintro; exact Hlgnn
  (try wp_auto)
  iapply HΦ
  iexact Hmsg))

set_option hygiene false in
/-- Fold `msgPtsC` back from its named components. -/
local macro "fold_msg" : tactic => `(tactic| (
  iunfold msgPtsC
  iexists pty, pto, pfr, pte, plt, pix, pco, pvo, prj, prh, es, els, ps, cs, rs, uf
  isplitr
  · ipureintro; exact Hnn
  iframe
  iframe cTy cTo cFr cTe cLt cIx cCo cVo cRj cRh Hents Hcs Hpb))

set_option hygiene false in
/-- The `MsgHeartbeatResp || MsgHeartbeat || MsgBeat` branch of `logRaftCommunication`. -/
local macro "heartbeat_branch" : tactic => `(tactic| (
  iunfold msgPtsC at Hmsg
  iNamed Hmsg
  (try wp_auto)
  wp_if_destruct
  · -- `cs.len = W64 8`: `!(cs.len == 8)` is false, so decode `cs` and run `debug_tail`
    (try wp_auto)
    ihave %Hclen := ownSlice_len _ _ _ $$ Hcs
    have Hlen8 : ms.ctx.length = 8 := by
      obtain ⟨h1', h2'⟩ := Hclen; revert Hif h1' h2'; word
    have Hbe := hBe cs ms.ctx [] DFrac.discard Hlen8
    rw [List.append_nil] at Hbe
    wp_apply Hbe $$ [] as -
    · iexact Hcs
    (try wp_auto)
    ihave Hmsg : msgPtsC m dq dqe cap ms $$
      [HTy HTo HFr HTe HLt HIx HCo HVo HRj HRh HEs Hes Hes_cap HSn Hsn HCx HRs Hrs]
    · fold_msg
    debug_tail
  · -- `cs.len ≠ W64 8`: early return
    (try wp_auto)
    iapply HΦ
    fold_msg))

set_option hygiene false in
/-- The `MsgReadIndexResp || MsgReadIndex` branch of `logRaftCommunication`. -/
local macro "readindex_branch" : tactic => `(tactic| (
  iunfold msgPtsC at Hmsg
  iNamed Hmsg
  (try wp_auto)
  ihave %Hel_len := ownSlice_len _ _ _ $$ Hes
  ihave %Hents_len := BigSepL2.bigSepL2_length $$ Hents
  wp_if_destruct
  · have Hlt0 : 0 < els.length := by obtain ⟨h1', h2'⟩ := Hel_len; revert Hif h1' h2'; word
    have Hpos_es : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z es.len := by
      obtain ⟨h1', h2'⟩ := Hel_len; revert Hlt0 h1' h2'; word
    have Hlt0_m : 0 < ms.ents.length := by omega
    obtain ⟨p0, Hp0⟩ : ∃ p0, els[0]? = some p0 := ⟨els[0]'Hlt0, List.getElem?_eq_some_iff.2 ⟨Hlt0, rfl⟩⟩
    obtain ⟨e0, He0⟩ : ∃ e0, ms.ents[0]? = some e0 := ⟨ms.ents[0]'Hlt0_m, List.getElem?_eq_some_iff.2 ⟨Hlt0_m, rfl⟩⟩
    ihave #Hp0_is := (BigSepL2.bigSepL2_lookup Hp0 He0) $$ Hents
    iunfold entRO at Hp0_is
    iunfold entPts at Hp0_is
    icases Hp0_is with ⟨%pt_e, %pi_e, %pty_e, %ds, %uf_e, %Hp0nn, #HT_e, #cT_e, #HI_e, #cI_e, #HY_e, #cY_e, #HD, #Hd, #Hpb_e⟩
    rw [ite_eq_left Hpos_es]
    wp_apply wp_load_slice_index es (sint.Z (W64 0)) els dqe p0 Hpos_es.1 $$ [Hes] as Hes
    · iframe Hes; ipureintro; simpa using Hp0
    (try wp_auto)
    wp_if_destruct
    · ihave %Hds_len := ownSlice_len _ _ _ $$ Hd
      have Hdlen8 : e0.Data'.length = 8 := by obtain ⟨h1', h2'⟩ := Hds_len; revert Hif h1' h2'; word
      rw [ite_eq_left Hpos_es]
      wp_apply wp_load_slice_index es (sint.Z (W64 0)) els dqe p0 Hpos_es.1 $$ [Hes] as Hes
      · iframe Hes; ipureintro; simpa using Hp0
      (try wp_auto)
      have Hbe := hBe ds e0.Data' [] DFrac.discard Hdlen8
      rw [List.append_nil] at Hbe
      wp_apply Hbe $$ [] as -
      · iexact Hd
      ihave Hmsg : msgPtsC m dq dqe cap ms $$
        [HTy HTo HFr HTe HLt HIx HCo HVo HRj HRh HEs Hes Hes_cap HSn Hsn HCx HRs Hrs]
      · fold_msg
      debug_tail
    · ihave Hmsg : msgPtsC m dq dqe cap ms $$
        [HTy HTo HFr HTe HLt HIx HCo HVo HRj HRh HEs Hes Hes_cap HSn Hsn HCx HRs Hrs]
      · fold_msg
      debug_tail
  · ihave Hmsg : msgPtsC m dq dqe cap ms $$
      [HTy HTo HFr HTe HLt HIx HCo HVo HRj HRh HEs Hes Hes_cap HSn Hsn HCx HRs Hrs]
    · fold_msg
    debug_tail))

theorem rafthttp.logRaftCommunication.wp_proof
    (hCore : zap.Logger.Core.spec (GF := GF) (hG := hG))
    (hGetType : raftpb.Message.GetType.spec (GF := GF) (hG := hG))
    (hGetTerm : raftpb.Message.GetTerm.spec (GF := GF) (hG := hG))
    (hGetIndex : raftpb.Message.GetIndex.spec (GF := GF) (hG := hG))
    (hGetCommit : raftpb.Message.GetCommit.spec (GF := GF) (hG := hG))
    (hMsgTypeStr : raftpb.MessageType.String.spec (GF := GF) (hG := hG))
    (hIDStr : types.ID.String_ptr.spec (GF := GF) (hG := hG))
    (hBe : binary.bigEndian.Uint64.spec (GF := GF) (hG := hG))
    (hUnm : proto.UnmarshalIRR.spec (GF := GF) (hG := hG))
    (hZS : zap.String.spec (GF := GF) (hG := hG))
    (hZU : zap.Uint64.spec (GF := GF) (hG := hG))
    (hZDebug : zap.Logger.Debug.spec (GF := GF) (hG := hG)) :
    rafthttp.logRaftCommunication.spec (GF := GF) (hG := hG) := by
  intro lg m localID remote direction dq dqe cap ms
  haveI : go.NotInterface go.int32 := ⟨by unfold go.int32; trivial⟩
  wp_start as ⟨%Hlgnn, Hmsg, %Hprop⟩
  ihave #Pzap : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
  · iPkgInit
  ihave #Ppb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb $$ []
  · iPkgInit
  ihave #Ptypes : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.pkg.v3.types $$ []
  · iPkgInit
  ihave #Pproto : isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.protobuf.proto $$ []
  · iPkgInit
  wp_auto
  wp_apply hCore lg $$ [] as %c ⟨%ci, %Hc, #Hci⟩
  · iframe #; ipureintro; exact Hlgnn
  subst Hc
  iunfold zap.coreSpec at Hci
  wp_auto
  wp_apply Hci as %b -
  cases b
  · wp_auto
    iapply HΦ
    iexact Hmsg
  wp_auto
  wp_apply hGetType.1 m dq dqe cap ms $$ [Hmsg] as Hmsg
  · iframe # Hmsg
  (try wp_auto)
  wp_if_destruct
  · heartbeat_branch
  wp_if_destruct
  · heartbeat_branch
  wp_if_destruct
  · heartbeat_branch
  wp_if_destruct
  · readindex_branch
  wp_if_destruct
  · readindex_branch
  wp_if_destruct
  · -- Branch 3: `MsgProp`
    have HtyProp : ms.msg.Type' = MsgProp := Hif
    iunfold msgPtsC at Hmsg
    iNamed Hmsg
    (try wp_auto)
    ihave %Hel_len := ownSlice_len _ _ _ $$ Hes
    ihave %Hents_len := BigSepL2.bigSepL2_length $$ Hents
    wp_if_destruct
    · have Hlt0 : 0 < els.length := by obtain ⟨h1', h2'⟩ := Hel_len; revert Hif h1' h2'; word
      have Hpos_es : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z es.len := by
        obtain ⟨h1', h2'⟩ := Hel_len; revert Hlt0 h1' h2'; word
      have Hlt0_m : 0 < ms.ents.length := by omega
      obtain ⟨p0, Hp0⟩ : ∃ p0, els[0]? = some p0 := ⟨els[0]'Hlt0, List.getElem?_eq_some_iff.2 ⟨Hlt0, rfl⟩⟩
      obtain ⟨e0, He0⟩ : ∃ e0, ms.ents[0]? = some e0 := ⟨ms.ents[0]'Hlt0_m, List.getElem?_eq_some_iff.2 ⟨Hlt0_m, rfl⟩⟩
      ihave #Hp0_is := (BigSepL2.bigSepL2_lookup Hp0 He0) $$ Hents
      iunfold entRO at Hp0_is
      iunfold entPts at Hp0_is
      icases Hp0_is with ⟨%pt_e, %pi_e, %pty_e, %ds, %uf_e, %Hp0nn, #HT_e, #cT_e, #HI_e, #cI_e, #HY_e, #cY_e, #HD, #Hd, #Hpb_e⟩
      rw [ite_eq_left Hpos_es]
      wp_apply wp_load_slice_index es (sint.Z (W64 0)) els dqe p0 Hpos_es.1 $$ [Hes] as Hes
      · iframe Hes; ipureintro; simpa using Hp0
      (try wp_auto)
      wp_apply hUnm ds e0.Data' r_ptr _ DFrac.discard $$ [r] as %err ⟨_, Herr⟩
      · iframe # r
      icases Herr with (⟨%Herr, %rq, %Hdec, #Hrq⟩ | %Hne)
      · subst Herr
        have Hhdr_some : rq.header.isSome := Hprop HtyProp e0 rq He0 Hdec
        obtain ⟨hm, Hhm⟩ := Option.isSome_iff_exists.1 Hhdr_some
        iunfold apply.internalRaftRequestIs at Hrq
        ihave ⟨%Hrnn, _, ⟨%lh, #Hlh_ptr, #Hlh⟩, _⟩ := Hrq
        rw [Hhm]
        iunfold apply.optReqIs at Hlh
        iunfold apply.headerIs at Hlh
        ihave ⟨%Hlhnn, #Hlh_id, _⟩ := Hlh
        (try wp_auto)
        ihave Hmsg : msgPtsC m dq dqe cap ms $$
          [HTy HTo HFr HTe HLt HIx HCo HVo HRj HRh HEs Hes Hes_cap HSn Hsn HCx HRs Hrs]
        · fold_msg
        debug_tail
      · cases err with
        | nil => exact absurd rfl Hne
        | ok ei =>
          (try wp_auto)
          ihave Hmsg : msgPtsC m dq dqe cap ms $$
            [HTy HTo HFr HTe HLt HIx HCo HVo HRj HRh HEs Hes Hes_cap HSn Hsn HCx HRs Hrs]
          · fold_msg
          debug_tail
    · ihave Hmsg : msgPtsC m dq dqe cap ms $$
        [HTy HTo HFr HTe HLt HIx HCo HVo HRj HRh HEs Hes Hes_cap HSn Hsn HCx HRs Hrs]
      · fold_msg
      debug_tail
  · -- Default branch
    debug_tail

end proof

end EtcdGrove
end Perennial

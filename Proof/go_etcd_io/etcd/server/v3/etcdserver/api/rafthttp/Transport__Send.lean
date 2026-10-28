/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/rafthttp/Transport__Send.lean`. Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Transport__Send
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.peer__send
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.remote__send
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.isMsgApp
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v2stats.ServerStats__SendAppendReq
public import Spec.google_golang_org.protobuf.proto.SizeMessage
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetTo
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetType
public import Spec.go_etcd_io.raft.v3.raftpb.MessageType__String
public import Spec.go_etcd_io.etcd.client.pkg.v3.types.ID__String
public import Spec.go_etcd_io.etcd.client.pkg.v3.types.ID__String_ptr
public import Spec.go_uber_org.zap.Logger__Debug
public import Spec.go_uber_org.zap.String

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.api go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Assumptions]

set_option hygiene false in
/-- The next message: the invariant at `n + 1` (the message `ml`, its bundle used or dropped). -/
local macro "next_msg" : tactic => `(tactic| (
  wp_for_post
  iframe
  iexists n + W64 1, ml, _
  simp only [named]
  iframe
  (try (iunfold trReadTok; iframe))
  ipureintro
  refine ⟨by rw [show sint.nat (n + W64 1) = sint.nat n + 1 by word], by constructor <;> word⟩))

set_option maxRecDepth 8000 in
set_option maxHeartbeats 8000000 in
theorem rafthttp.Transport.Send.wp_proof
    (hPeerSend : rafthttp.peer.send.spec (GF := GF) (hG := hG))
    (hRemoteSend : rafthttp.remote.send.spec (GF := GF) (hG := hG))
    (hIsApp : rafthttp.isMsgApp.spec (GF := GF) (hG := hG))
    (hSendApp : v2stats.ServerStats.SendAppendReq.spec (GF := GF) (hG := hG))
    (hSize : proto.SizeMessage.spec (GF := GF) (hG := hG))
    (hGetTo : raftpb.Message.GetTo.spec (GF := GF) (hG := hG))
    (hGetType : raftpb.Message.GetType.spec (GF := GF) (hG := hG))
    (hTypeString : raftpb.MessageType.String.spec (GF := GF) (hG := hG))
    (hIDString : types.ID.String.spec (GF := GF) (hG := hG))
    (hIDStringPtr : types.ID.String_ptr.spec (GF := GF) (hG := hG))
    (hDebug : zap.Logger.Debug.spec (GF := GF) (hG := hG))
    (hZString : zap.String.spec (GF := GF) (hG := hG)) :
    rafthttp.Transport.Send.spec (GF := GF) (hG := hG) := by
  intro Rh t lid γd R γs γr sl msL
  wp_start as ⟨#Htr, Htok, Hsl, Hms⟩
  ihave #Htr' := Htr
  iunfold trFixed at Htr'
  icases Htr' with ⟨%lg, %ls, %ss, %turls, %tuvs, %cid, %r, %ec, %srt, %prt, %drf, %ppr, %spr, #Hlg, %Hlgnn,
    #Hlid, #HtURLs, #Htuvs, #Hcid, #Hr, #Hraft, #Hec, #Hsrt, #Hsrtok, #Hprt, #Hprtok, #Hdrf, #Hls,
    %Hlsnn, #Hss, %Hssnn, #Hppr, #Hspr, #Hreg, #Hpreg, #HPfx, %HmemU⟩
  obtain ⟨Hmem, Hturls⟩ := HmemU
  wp_auto
  ihave %Hsll := ownSlice_len $$ Hsl
  ipersist Hsl
  ihave IH : iprop(∃ (n : w64) (m0 : Loc) (rest : List Loc),
      "i" ∷ i_ptr ↦ n ∗ "m" ∷ m_ptr ↦ m0 ∗ "Htok" ∷ trReadTok Rh t lid γd R γs γr ∗
      "Hms" ∷ ([∗list] mm ∈ rest, sendMsg Rh lid mm) ∗
      "%Hr" ∷ ⌜msL.drop (sint.nat n) = rest⌝ ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ (msL.length : Int)⌝) $$ [i m Htok Hms]
  · iexists W64 0, _, msL
    simp only [named]
    iframe
    ipureintro; exact ⟨rfl, by constructor <;> word⟩
  wp_for IH
  wp_if_destruct
  · have Hlt : sint.nat n < msL.length := by word
    obtain ⟨ml, Hml⟩ : ∃ ml, msL[sint.nat n]? = some ml := ⟨_, List.getElem?_eq_getElem Hlt⟩
    have Hbi : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z sl.len := ⟨Hn.1, by word⟩
    (try wp_auto)
    rw [ite_eq_left Hbi]
    icases ownSlice_elem_acc (sint.Z n) ml sl DFrac.discard msL Hn.1 Hml $$ Hsl with ⟨#Hel, -⟩
    (try wp_auto)
    -- the message's bundle
    have Hdrop : msL.drop (sint.nat n) = ml :: msL.drop (sint.nat n + 1) := by
      rw [List.drop_eq_getElem_cons Hlt]
      rw [List.getElem?_eq_getElem Hlt] at Hml
      cases Hml; rfl
    rw [Hdrop] at Hr
    subst Hr
    icases BigSepL.bigSepL_cons.1 $$ Hms with ⟨Hm1, Hms⟩
    iunfold sendMsg at Hm1
    icases Hm1 with ⟨%st, #Hmo, #HP, HO, %Hst⟩
    wp_apply hGetTo.1 ml _ _ _ st $$ [] as -
    · iframe #
    (try wp_auto)
    by_cases h0 : st.msg.To' = W64 0
    · rw [_root_.decide_eq_true h0]
      (try wp_auto)
      next_msg
    rw [_root_.decide_eq_false h0]
    (try wp_auto)
    wp_apply hGetTo.1 ml _ _ _ st $$ [] as -
    · iframe #
    (try wp_auto)
    iunfold trReadTok at Htok
    wp_apply sync.RWMutex.wp_RLock $$ [$Htok] as ⟨Hrl, HP⟩
    iunfold trLockP at HP
    icases HP with ⟨%pm, %rm, %PM, %RM, %T, %rs, %sb, Hp, Hr, Hpm, Hrm, Hg, Hgr, %Hrs, #Hpo, #Hro,
    Hts⟩
    (try wp_auto)
    wp_apply wp_lookup2_mapOrNil _ pm _ PM st.msg.To' $$ [$Hpm] as Hpm
    (try wp_auto)
    wp_apply wp_lookup2_mapOrNil _ rm _ RM st.msg.To' $$ [$Hrm] as Hrm
    (try wp_auto)
    wp_apply sync.RWMutex.wp_RUnlock $$ [$Hrl Hp Hr Hpm Hrm Hg Hgr Hts] as Htok
    · iunfold trLockP; iexists pm, rm, PM, RM, T, rs, sb; iframe; iframe #
      (try inext)
      ipureintro; exact Hrs
    (try wp_auto)
    cases hp : PM !! st.msg.To' with
    | some pi =>
      -- a peer: `p.send(m)`, after `SendAppendReq` for a `MsgApp`
      iunfold peersOk at Hpo
      ihave Hpi := BigSepM.bigSepM_lookup (Φ := fun id pi => iprop(∃ p : Loc,
        ⌜pi = interface.mkOk (go.GoType.PointerType rafthttp.peer.ty) #p⌝ ∗
        peerOk Rh lid id γd R p)) hp $$ Hpo
      icases Hpi with ⟨%pp, %Hpp, #Hpok⟩
      subst Hpp
      simp only [Option.getD_some, Option.isSome_some, _root_.decide_true]
      (try wp_auto)
      wp_apply hIsApp ml st $$ []
      · iframe #
      (try wp_auto)
      ihave #Hpp : isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.protobuf.proto $$ []
      · iPkgInit
      ihave #Hv2 : isPkgInit (PROP := IProp GF)
          pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v2stats $$ []
      · iPkgInit
      by_cases ha : st.msg.Type' = MsgApp
      · rw [_root_.decide_eq_true ha]
        (try wp_auto)
        wp_apply hSize ml _ _ _ st $$ [] as %sz -
        · iframe #
        wp_apply hSendApp ss sz $$ []
        · iframe #; ipureintro; exact Hssnn
        (try wp_auto)
        wp_apply hPeerSend Rh lid st.msg.To' γd R pp ml $$ [HO]
        · iframe #
          iunfold peerMsg; iexists st; iframe; iframe #; ipureintro
          exact ⟨Hst.1, rfl, Hst.2.1, Hst.2.2.1, Hst.2.2.2.1, Hst.2.2.2.2⟩
        (try wp_auto)
        next_msg
      · rw [_root_.decide_eq_false ha]
        (try wp_auto)
        wp_apply hPeerSend Rh lid st.msg.To' γd R pp ml $$ [HO]
        · iframe #
          iunfold peerMsg; iexists st; iframe; iframe #; ipureintro
          exact ⟨Hst.1, rfl, Hst.2.1, Hst.2.2.1, Hst.2.2.2.1, Hst.2.2.2.2⟩
        (try wp_auto)
        next_msg
    | none =>
      simp only [Option.getD_none, Option.isSome_none, Bool.false_eq_true, _root_.decide_false]
      (try wp_auto)
      cases hr : RM !! st.msg.To' with
      | some g =>
        iunfold remotesOk at Hro
        ihave #Hg := BigSepM.bigSepM_lookup
          (Φ := fun id g => iprop(remoteOk Rh lid id R g)) hr $$ Hro
        simp only [Option.getD_some, Option.isSome_some, _root_.decide_true]
        (try wp_auto)
        wp_apply hRemoteSend Rh lid st.msg.To' R g ml $$ [HO]
        · iframe #
          iunfold pipeMsg; iexists st; iframe; iframe #; ipureintro
          exact ⟨Hst.1, rfl, Hst.2.1, Hst.2.2.1⟩
        (try wp_auto)
        next_msg
      | none =>
        simp only [Option.getD_none, Option.isSome_none, Bool.false_eq_true, _root_.decide_false]
        (try wp_auto)
        rw [_root_.decide_eq_false Hlgnn]
        haveI : go.NotInterface go.int32 := ⟨by unfold go.int32; trivial⟩
        haveI : go.NotInterface go.uint64 := ⟨by unfold go.uint64; trivial⟩
        repeat' (first
          | (wp_apply hGetType.1 ml _ _ _ st $$ [] as -; iframe #)
          | (ihave #HT := hTypeString st.msg.Type'
             iunfold fmt.stringMethodSpec at HT
             wp_apply HT as %_)
          | (wp_apply hIDString as %_ -)
          | (wp_apply hIDStringPtr _ _ _ $$ [to] as %_ ⟨to, -⟩; iexact to)
          | (wp_apply hZString as %_ -)
          | (wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field); isplitr;
              (ipureintro; rfl); iintro %_ ⟨-, -⟩)
          | (wp_apply hDebug lg _ _ $$ []; (iframe #; ipureintro; exact Hlgnn))
          | wp_auto)
        next_msg
  · (try wp_auto)
    iapply HΦ; iexact Htok

end proof

end EtcdGrove
end Perennial

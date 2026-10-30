/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/rafthttp/msgAppV2Encoder__encode.lean`.
Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.msgAppV2Encoder__encode
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.isLinkHeartbeatMessage
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetIndex
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetLogTerm
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetTerm
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetCommit
public import Spec.go_etcd_io.raft.v3.raftpb.Entry__GetIndex
public import Spec.google_golang_org.protobuf.proto.SizePb
public import Spec.google_golang_org.protobuf.proto.MarshalAppendPb
public import Spec.go_etcd_io.etcd.pkg.v3.pbutil.MustMarshalMessage
public import Spec.encoding.binary.WriteUint8
public import Spec.encoding.binary.WriteUint64
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v2stats.FollowerStats__Succ
public import Perennial.Spec.time.Now
public import Perennial.Spec.time.Since
public import Perennial.Proof.encoding.binary.Results

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Assumptions]

set_option hygiene false in
/-- An error returned: the writer at some bytes, the encoder at its state, its tag buffer `x1`. -/
local macro "enc_err" : tactic => `(tactic| (
  wp_auto
  iapply HΦ
  isplitr
  · first | iapply http.errStrOk_nil | iassumption
  iexists _, cst
  iframe HWr
  isplitl
  · iunfold v2EncOwn
    iexists buf, s8, s1, zs, x8, x1
    iframe; iframe #; iframe %
  iintro %h0; cases h0))

set_option hygiene false in
/-- The App frame (`msgTypeApp`): the tag, then `messageEncoder`'s frame of the message, the
state the message's term and its last entry's index. -/
local macro "enc_full" : tactic => `(tactic| (
  have Hpe := pbEnc_ok (pbMessage (GF := GF)) ml st
  simp only [pbMessage_ro, pbMessage_marshals, pbMessage_wire, pbMessage_ty] at Hpe
  ihave %Hp := Hpe $$ Hm
  have Hwire := Hp.1 Hok.1
  have Hfr := V2Frame.full (frm := frm) (to := to) cst Hwire Hp.2
  ihave #Hbin : isPkgInit (PROP := IProp GF) pkg_id.encoding.binary $$ []
  · iPkgInit
  ihave %Hbe := bigEndian_ne_null $$ Hbin
  wp_apply (encoding.binary.wp_load_struct_nofields (V := encoding.binary.bigEndian)
    (globalAddr encoding.binary.BigEndian) Hbe)
  iintro -
  (try wp_auto)
  simp only [go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.msgTypeApp]
  ihave Hbw := wp_WriteUint8 go.uint8 wi (W8 2) iprop(Wr h)
    (fun n err => iprop(∃ k : Nat, Wr (h ++ ([W8 2]).take k) ∗
      ⌜sint.Z n = k ∧ k ≤ 1 ∧ (err = GoInterface.nil → k = 1)⌝ ∗ http.errStrOk err)) $$ []
  · iintro !> %sl !> %Φ ⟨Hsl, HWr⟩ HΦ
    ihave #HA1 : □ A (h ++ [W8 2]) $$ []
    · imodintro
      ihave H := HA $$ %_ %_ %1 %Hfr
      rw [show h ++ [W8 2] = h ++ List.take 1 (W8 2 :: msgFrame (pbEnc raftpb.Message.ty ml))
        from rfl]
      iexact H
    wp_apply Hwr $$ %sl %(DFrac.own 1) %([W8 2]) %h [Hsl HWr] as %n %err ⟨%k, -, HWr, %Hk, #Herr⟩
    · iframe; iframe #
    iapply HΦ; iexists k; iframe; iframe #; ipureintro; simpa using Hk
  wp_apply Hbw $$ [HWr] as %err ⟨%n, %k, HWr, %Hk, #Herr⟩
  · iframe
  cases err with
  | ok ei => enc_err
  | nil =>
  have hk : k = 1 := Hk.2.2 rfl
  subst hk
  (try wp_auto)
  ihave #Hbin : isPkgInit (PROP := IProp GF) pkg_id.encoding.binary $$ []
  · iPkgInit
  ihave %Hbe := bigEndian_ne_null $$ Hbin
  wp_apply (encoding.binary.wp_load_struct_nofields (V := encoding.binary.bigEndian)
    (globalAddr encoding.binary.BigEndian) Hbe)
  iintro -
  (try wp_auto)
  have wpS := wp_Size pbMessage ml st
  simp only [pbMessage_ty, pbMessage_ro] at wpS
  wp_apply wpS $$ [] as %n ⟨%Hn, -⟩
  · iexact Hm
  have hn : n = W64 (pbEnc raftpb.Message.ty ml).length := by word
  subst hn
  ihave Hbw := wp_WriteUint64 wi (W64 (pbEnc raftpb.Message.ty ml).length)
    iprop(Wr (h ++ [W8 2]))
    (fun n err => iprop(∃ k : Nat,
      Wr (h ++ [W8 2] ++ (u64Be (W64 (pbEnc raftpb.Message.ty ml).length)).take k) ∗
      ⌜sint.Z n = k ∧ k ≤ 8 ∧ (err = GoInterface.nil → k = 8)⌝ ∗ http.errStrOk err)) $$ []
  · iintro !> %sl !> %Φ ⟨Hsl, HWr⟩ HΦ
    ihave #HA1 : □ A (h ++ [W8 2] ++ u64Be (W64 (pbEnc raftpb.Message.ty ml).length)) $$ []
    · imodintro
      ihave H := HA $$ %_ %_ %9 %Hfr
      rw [show h ++ [W8 2] ++ u64Be (W64 (pbEnc raftpb.Message.ty ml).length) =
          h ++ List.take 9 (W8 2 :: msgFrame (pbEnc raftpb.Message.ty ml)) by
        simp [msgFrame, List.take_append_of_le_length, u64Be_length]]
      iexact H
    wp_apply Hwr $$ %sl %(DFrac.own 1) %(u64Be (W64 (pbEnc raftpb.Message.ty ml).length))
      %(h ++ [W8 2]) [Hsl HWr] as %n %err ⟨%k, -, HWr, %Hk, #Herr⟩
    · iframe; iframe #
    iapply HΦ; iexists k; iframe; iframe #; ipureintro; simpa [u64Be_length] using Hk
  wp_apply Hbw $$ [HWr] as %err ⟨%n, %k, HWr, %Hk, #Herr⟩
  · iframe
  cases err with
  | ok ei => enc_err
  | nil =>
  have hk : k = 8 := Hk.2.2 rfl
  subst hk
  rw [List.take_of_length_le (by simp [u64Be_length])] at *
  (try wp_auto)
  have wpM := wp_MustMarshalMessage pbMessage ml st Hok.1
  simp only [pbMessage_ty, pbMessage_ro, pbMessage_wire] at wpM
  wp_apply wpM $$ [] as %d ⟨Hd, -, -⟩
  · iexact Hm
  (try wp_auto)
  ihave #HA1 : □ A (h ++ [W8 2] ++ u64Be (W64 (pbEnc raftpb.Message.ty ml).length) ++
      pbEnc raftpb.Message.ty ml) $$ []
  · imodintro
    ihave H := HA $$ %_ %_ %(9 + (pbEnc raftpb.Message.ty ml).length) %Hfr
    rw [show h ++ [W8 2] ++ u64Be (W64 (pbEnc raftpb.Message.ty ml).length) ++
          pbEnc raftpb.Message.ty ml =
        h ++ List.take (9 + (pbEnc raftpb.Message.ty ml).length)
          (W8 2 :: msgFrame (pbEnc raftpb.Message.ty ml)) by
      rw [List.take_of_length_le (by simp [msgFrame, u64Be_length]; omega)]
      simp [msgFrame]]
    iexact H
  wp_apply Hwr $$ %d %(DFrac.own 1) %(pbEnc raftpb.Message.ty ml)
    %(h ++ [W8 2] ++ u64Be (W64 (pbEnc raftpb.Message.ty ml).length)) [Hd HWr]
    as %n %err ⟨%k, -, HWr, %Hk, #Herr⟩
  · iframe; iframe #
  (try wp_auto)
  cases err with
  | ok ei => enc_err
  | nil =>
  have hk : k = (pbEnc raftpb.Message.ty ml).length := Hk.2.2 rfl
  subst hk
  rw [List.take_of_length_le (Nat.le_refl _)]
  (try wp_auto)
  wp_apply wp_GetTerm.1 ml DFrac.discard DFrac.discard false st $$ [] as -
  · iexact Hm
  (try wp_auto)
  wp_apply wp_GetIndex.1 ml DFrac.discard DFrac.discard false st $$ [] as -
  · iexact Hm
  (try wp_auto)
  ihave Hm2 := Hm
  iunfold msgOwn at Hm2
  iunfold msgPts at Hm2
  iunfold msgPtsC at Hm2
  iNamed Hm2
  ihave %Hesl := ownSlice_len _ _ _ $$ Hes
  ihave %Hel := BigSepL2.bigSepL2_length $$ Hents
  (try wp_auto)
  wp_join iprop(∃ ix : w64, enc_ptr ↦ enc ∗
      enc.[go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.msgAppV2Encoder,
      go!"index"] ↦ ix ∗ ⌜ix = lastIdx (wireOf st)⌝) with [Hindex enc m l Hes HEs]
      as ⟨%ix, enc, Hindex, %Hix⟩
  · (try wp_auto)
    -- the last entry's index (`wp_auto` closes the case of no entries)
    · have hpos : 0 < sint.nat es.len := by
        have h0 : sint.Z (W64 0) = 0 := rfl
        word
      obtain ⟨p, Hp⟩ : ∃ p, els[sint.nat es.len - 1]? = some p :=
        ⟨_, List.getElem?_eq_getElem (by omega)⟩
      obtain ⟨e, He⟩ : ∃ e, st.ents[sint.nat es.len - 1]? = some e :=
        ⟨_, List.getElem?_eq_getElem (by omega)⟩
      ihave #Hep := BigSepL2.bigSepL2_lookup Hp He $$ Hents
      (try wp_auto)
      have hlen : 0 < sint.Z es.len := Hif
      rw [if_pos (sint_sub_one_bounds hlen)]
      wp_apply (wp_load_slice_index (V := Loc) es _ els DFrac.discard p
        (sint_sub_one_bounds hlen).1) $$ [Hes] as Hes
      · iframe; iframe #; ipureintro; rw [sint_sub_one_toNat hlen]; exact Hp
      (try wp_auto)
      wp_apply wp_Entry_GetIndex.1 p DFrac.discard e $$ [] as -
      · iexact Hep
      (try wp_auto)
      iframe
      ipureintro
      refine ⟨rfl, ?_⟩
      simp only [lastIdx, wireOf]
      rw [List.getLast?_eq_getElem?, show st.ents.length - 1 = sint.nat es.len - 1 by omega, He]
  · -- no entries: the message's index
    iexists _; iframe
    ipureintro
    have h0 : sint.Z (W64 0) = 0 := rfl
    have : st.ents = [] := List.eq_nil_of_length_eq_zero (by word)
    simp [lastIdx, wireOf, this]
  (try wp_auto)
  wp_apply wp_Since as %d -
  (try wp_auto)
  wp_apply wp_Succ fs d $$ []
  · ipureintro; exact Hfsnn
  (try wp_auto)
  subst Hix
  iapply HΦ
  isplitr
  · first | iapply http.errStrOk_nil | iassumption
  iexists _, ⟨st.msg.Term', lastIdx (wireOf st)⟩
  iframe HWr
  isplitl
  · iunfold v2EncOwn
    iexists buf, s8, s1, zs, x8, x1
    iframe; iframe #; iframe %
  iintro -
  ipureintro
  exact ⟨_, Hfr, by simp [msgFrame]⟩))

set_option maxHeartbeats 2000000 in
theorem rafthttp.msgAppV2Encoder.encode.wp_proof
    (wp_Now : time.Now.spec (GF := GF) (hG := hG))
    (wp_Since : time.Since.spec (GF := GF) (hG := hG))
    (wp_isLinkHeartbeatMessage : rafthttp.isLinkHeartbeatMessage.spec (GF := GF) (hG := hG))
    (wp_GetIndex : raftpb.Message.GetIndex.spec (GF := GF) (hG := hG))
    (wp_GetLogTerm : raftpb.Message.GetLogTerm.spec (GF := GF) (hG := hG))
    (wp_GetTerm : raftpb.Message.GetTerm.spec (GF := GF) (hG := hG))
    (wp_GetCommit : raftpb.Message.GetCommit.spec (GF := GF) (hG := hG))
    (wp_Entry_GetIndex : raftpb.Entry.GetIndex.spec (GF := GF) (hG := hG))
    (wp_Size : proto.SizePb.spec (GF := GF) (hG := hG))
    (wp_MarshalAppend : proto.MarshalAppendPb.spec (GF := GF) (hG := hG))
    (wp_MustMarshalMessage : pbutil.MustMarshalMessage.spec (GF := GF) (hG := hG))
    (wp_WriteUint8 : binary.WriteUint8.spec (GF := GF) (hG := hG))
    (wp_WriteUint64 : binary.WriteUint64.spec (GF := GF) (hG := hG))
    (wp_Succ : v2stats.FollowerStats.Succ.spec (GF := GF) (hG := hG)) :
    rafthttp.msgAppV2Encoder.encode.spec (GF := GF) (hG := hG) := by
  intro enc wi fs cst frm to ml st Wr A h Hok
  wp_start as ⟨Henc, #Hwr, HWr, #Hm, #HA⟩
  iunfold writerAt at Hwr
  iunfold v2EncOwn at Henc
  iNamed Henc
  wp_auto
  wp_apply wp_Now as %t -
  (try wp_auto)
  wp_apply wp_isLinkHeartbeatMessage ml DFrac.discard DFrac.discard false st $$ [] as -
  · iexact Hm
  (try wp_auto)
  by_cases hb : isHB st.msg
  · -- the link heartbeat: the byte `0`
    rw [decide_eq_true (p := isHB st.msg) hb]
    ihave %Hs1l := ownSlice_len _ _ _ $$ Hs1s
    have hx1 : ∃ b, x1 = [b] := by
      match x1, Hx1 with
      | [b], _ => exact ⟨b, rfl⟩
    obtain ⟨b, rfl⟩ := hx1
    wp_auto
    rw [if_pos (by simp at Hs1l; word)]
    simp only [show sint.Z (W64 0) = 0 from rfl,
      go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.msgTypeLinkHeartbeat]
    wp_apply wp_store_slice_index (V := w8) s1 0 [b] (W8 0) $$ [$Hs1s] as Hs1s
    · ipureintro; simp
    rw [show [b].set (Int.toNat 0) (W8 0) = [W8 0] from rfl]
    (try wp_auto)
    ihave #HA0 : □ A (h ++ [W8 0]) $$ []
    · imodintro
      ihave H := HA $$ %([W8 0]) %cst %1 %(Hok.hb_frame cst hb)
      rw [show h ++ [W8 0] = h ++ List.take 1 [W8 0] from rfl]
      iexact H
    wp_apply Hwr $$ %s1 %(DFrac.own 1) %([W8 0]) %h [$Hs1s $HWr $HA0] as %n %err ⟨%k, Hs1s, HWr, %Hk, #Herr⟩
    (try wp_auto)
    cases err with
    | ok ei =>
      wp_auto
      iapply HΦ
      isplitr
      · first | iapply http.errStrOk_nil | iassumption
      iexists _, cst
      iframe HWr
      isplitl
      · iunfold v2EncOwn
        iexists buf, s8, s1, zs, x8, [W8 0]
        have : [W8 0].length = 1 := rfl
        iframe; iframe #; iframe %
      iintro %h0; cases h0
    | nil =>
      wp_auto
      iapply HΦ
      isplitr
      · first | iapply http.errStrOk_nil | iassumption
      iexists _, cst
      iframe HWr
      isplitl
      · iunfold v2EncOwn
        iexists buf, s8, s1, zs, x8, [W8 0]
        have : [W8 0].length = 1 := rfl
        iframe; iframe #; iframe %
      iintro -
      ipureintro
      refine ⟨[W8 0], Hok.hb_frame cst hb, ?_⟩
      rw [List.take_of_length_le (by simp [Hk.2.2 rfl])]
  · rw [decide_eq_false (p := isHB st.msg) hb]
    wp_auto
    wp_apply wp_GetIndex.1 ml DFrac.discard DFrac.discard false st $$ [] as -
    · iexact Hm
    (try wp_auto)
    by_cases c1 : cst.index = st.msg.Index'
    · rw [decide_eq_true (p := cst.index = st.msg.Index') c1]
      wp_auto
      wp_apply wp_GetLogTerm.1 ml DFrac.discard DFrac.discard false st $$ [] as -
      · iexact Hm
      (try wp_auto)
      by_cases c2 : cst.term = st.msg.LogTerm'
      · rw [decide_eq_true (p := cst.term = st.msg.LogTerm') c2]
        wp_auto
        wp_apply wp_GetLogTerm.1 ml DFrac.discard DFrac.discard false st $$ [] as -
        · iexact Hm
        (try wp_auto)
        wp_apply wp_GetTerm.1 ml DFrac.discard DFrac.discard false st $$ [] as -
        · iexact Hm
        (try wp_auto)
        by_cases c3 : st.msg.LogTerm' = st.msg.Term'
        · rw [decide_eq_true (p := st.msg.LogTerm' = st.msg.Term') c3]
          wp_auto
          -- the AppEntries frame: its bytes, of the entries' encodings
          ihave ⟨%es, %els, #HEs, #Hes, #Hents⟩ := msgOwn_ents ml st $$ Hm
          ihave %Hesl := ownSlice_len _ _ _ $$ Hes
          ihave %Hel := BigSepL2.bigSepL2_length $$ Hents
          ihave %He := ents_enc els st.ents $$ Hents
          have Hn : st.ents.length < 2 ^ 63 := by
            have := Hesl.1; unfold sint.nat at this; word
          have Hfr := Hok.short_frame (cs := cst) hb c1 c2 c3 He Hn
          -- the tag
          ihave %Hs1l := ownSlice_len _ _ _ $$ Hs1s
          have hx1 : ∃ b, x1 = [b] := by
            match x1, Hx1 with
            | [b], _ => exact ⟨b, rfl⟩
          obtain ⟨b, rfl⟩ := hx1
          (try wp_auto)
          rw [if_pos (by simp at Hs1l; word)]
          simp only [show sint.Z (W64 0) = 0 from rfl,
            go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.msgTypeAppEntries]
          wp_apply wp_store_slice_index (V := w8) s1 0 [b] (W8 1) $$ [$Hs1s] as Hs1s
          · ipureintro; simp
          rw [show [b].set (Int.toNat 0) (W8 1) = [W8 1] from rfl]
          (try wp_auto)
          ihave #HA0 : □ A (h ++ [W8 1]) $$ []
          · imodintro
            ihave H := HA $$ %_ %_ %1 %Hfr
            rw [show h ++ [W8 1] = h ++ List.take 1 (shortBytes (els.map (pbEnc raftpb.Entry.ty)) st.msg.Commit') from rfl]
            iexact H
          wp_apply Hwr $$ %s1 %(DFrac.own 1) %([W8 1]) %h [$Hs1s $HWr $HA0]
            as %n %err ⟨%k, Hs1s, HWr, %Hk, #Herr⟩
          (try wp_auto)
          have Hx1' : [W8 1].length = 1 := rfl
          cases err with
          | ok ei =>
            wp_auto
            iapply HΦ
            isplitr
            · first | iapply http.errStrOk_nil | iassumption
            iexists _, cst
            iframe HWr
            isplitl
            · iunfold v2EncOwn
              iexists buf, s8, s1, zs, x8, [W8 1]
              iframe; iframe #; iframe %
            iintro %h0; cases h0
          | nil =>
          have hk : k = 1 := Hk.2.2 rfl
          subst hk
          rw [show List.take 1 [W8 1] = [W8 1] from rfl]
          wp_auto
          -- the count
          have hes : es.len = W64 st.ents.length := by
            have := Hesl.1; unfold sint.nat at this; rw [← Hel, this]; word
          wp_apply encoding.binary.wp_BigEndian_PutUint64 s8 x8 [] es.len Hx8 $$ [Hs8s] as Hs8s
          · simp only [List.append_nil]; iexact Hs8s
          simp only [List.append_nil]
          rw [hes]
          (try wp_auto)
          -- every prefix of the frame is permitted
          ihave #HAp : □ (∀ p : List w8,
              ⌜p <+: shortBytes (els.map (pbEnc raftpb.Entry.ty)) st.msg.Commit'⌝ -∗ A (h ++ p)) $$ []
          · iintro !> %p %hp
            rw [List.prefix_iff_eq_take.1 hp]
            iapply HA $$ %_ %_ %_ %Hfr
          have hEl : (els.map (pbEnc raftpb.Entry.ty)).length = st.ents.length := by simp [Hel]
          ihave #HA9 : □ A (h ++ [W8 1] ++ (u64Le (W64 st.ents.length)).reverse) $$ []
          · imodintro
            rw [List.append_assoc]
            iapply HAp
            ipureintro
            simp only [shortBytes, hEl]
            exact ⟨entFrames (els.map (pbEnc raftpb.Entry.ty)) ++ u64Be st.msg.Commit',
              by simp [u64Be, List.append_assoc]⟩
          wp_apply Hwr $$ %s8 %(DFrac.own 1) %((u64Le (W64 st.ents.length)).reverse) %(h ++ [W8 1])
            [$Hs8s $HWr $HA9] as %n %err ⟨%k, Hs8s, HWr, %Hk, #Herr⟩
          (try wp_auto)
          have Hx8' : ((u64Le (W64 st.ents.length)).reverse).length = 8 := by simp [u64Le_length]
          cases err with
          | ok ei =>
            wp_auto
            iapply HΦ
            isplitr
            · first | iapply http.errStrOk_nil | iassumption
            iexists _, cst
            iframe HWr
            isplitl
            · iunfold v2EncOwn
              iexists buf, s8, s1, zs, (u64Le (W64 st.ents.length)).reverse, [W8 1]
              iframe; iframe #; iframe %
            iintro %h0; cases h0
          | nil =>
          have hk : k = 8 := by have := Hk.2.2 rfl; simpa [u64Le_length] using this
          subst hk
          rw [List.take_of_length_le (by simp [u64Le_length])]
          wp_auto
          -- the entries
          ihave HI : (∃ (j : Nat) (zs' x8' : List w8),
              "i" ∷ i_ptr ↦ W64 j ∗
              "HWr" ∷ Wr (h ++ [W8 1] ++ (u64Le (W64 st.ents.length)).reverse ++
                entFrames ((els.map (pbEnc raftpb.Entry.ty)).take j)) ∗
              "Hindex" ∷ enc.[go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.msgAppV2Encoder,
                go!"index"] ↦ (cst.index + W64 j) ∗
              "Hbufs" ∷ buf ↦* zs' ∗ "Hbufc" ∷ ownSliceCap w8 buf (DFrac.own 1) ∗
              "Hs8s" ∷ s8 ↦* x8' ∗ "%Hx8'" ∷ ⌜x8'.length = 8⌝ ∗
              "%Hj" ∷ ⌜j ≤ st.ents.length⌝ : IProp GF) $$ [i HWr Hindex Hbufs Hbufc Hs8s]
          · iexists 0, zs, (u64Le (W64 st.ents.length)).reverse
            simp only [List.take_zero, entFrames, List.append_nil]
            rw [show cst.index + W64 ((0 : Nat) : Int) = cst.index by word]
            iframe
            ipureintro; exact ⟨Hx8', Nat.zero_le _⟩
          wp_for HI
          have hn64 : st.ents.length < 2 ^ 63 := Hn
          have hesn : sint.Z es.len = st.ents.length := by rw [hes]; word
          wp_if_destruct
          · -- the `j`-th entry
            have hj : j < st.ents.length := by
              have : sint.Z (W64 (j : Int)) = j := by word
              omega
            obtain ⟨p, Hp⟩ : ∃ p, els[j]? = some p := ⟨_, List.getElem?_eq_getElem (by omega)⟩
            obtain ⟨e, He'⟩ : ∃ e, st.ents[j]? = some e := ⟨_, List.getElem?_eq_getElem hj⟩
            ihave #Hep := BigSepL2.bigSepL2_lookup Hp He' $$ Hents
            (try wp_auto)
            have hjz : sint.Z (W64 (j : Int)) = j := by word
            rw [if_pos (by rw [hjz]; omega)]
            wp_apply (wp_load_slice_index (V := Loc) es _ els DFrac.discard p (by rw [hjz]; omega))
              $$ [Hes] as Hes
            · iframe; iframe #; ipureintro; rw [hjz]; exact Hp
            (try wp_auto)
            have wpSE := wp_Size pbEntry p e
            simp only [pbEntry_ty, pbEntry_ro] at wpSE
            wp_apply wpSE $$ [] as %sz ⟨%Hsz, -⟩
            · iexact Hep
            (try wp_auto)
            -- the facts of the `j`-th encoding
            have HEj : (els.map (pbEnc raftpb.Entry.ty))[j]'(by simp [Hel]; omega) =
                pbEnc raftpb.Entry.ty p := by
              simp [List.getElem_map, (List.getElem?_eq_some_iff.1 Hp).2]
            have hEj := shortBytes_split (els.map (pbEnc raftpb.Entry.ty)) st.msg.Commit' j
              (by simp [Hel]; omega)
            rw [HEj] at hEj
            have hsz : sz = W64 (pbEnc raftpb.Entry.ty p).length := by word
            subst hsz
            wp_apply encoding.binary.wp_BigEndian_PutUint64 s8 x8' [] _ Hx8' $$ [Hs8s] as Hs8s
            · simp only [List.append_nil]; iexact Hs8s
            simp only [List.append_nil]
            (try wp_auto)
            ihave #HAs : □ A (h ++ [W8 1] ++ (u64Le (W64 st.ents.length)).reverse ++
                entFrames ((els.map (pbEnc raftpb.Entry.ty)).take j) ++
                (u64Le (W64 (pbEnc raftpb.Entry.ty p).length)).reverse) $$ []
            · imodintro
              ihave H := HAp $$ %([W8 1] ++ (u64Le (W64 st.ents.length)).reverse ++
                entFrames ((els.map (pbEnc raftpb.Entry.ty)).take j) ++
                (u64Le (W64 (pbEnc raftpb.Entry.ty p).length)).reverse) %(by
                  rw [hEj, hEl]
                  exact ⟨pbEnc raftpb.Entry.ty p ++
                    entFrames ((els.map (pbEnc raftpb.Entry.ty)).drop (j + 1)) ++
                    u64Be st.msg.Commit', by simp [u64Be, List.append_assoc]⟩)
              simp only [List.append_assoc] at *
              iexact H
            wp_apply Hwr $$ %s8 %(DFrac.own 1) %((u64Le (W64 (pbEnc raftpb.Entry.ty p).length)).reverse)
              %(h ++ [W8 1] ++ (u64Le (W64 st.ents.length)).reverse ++
                entFrames ((els.map (pbEnc raftpb.Entry.ty)).take j)) [$Hs8s $HWr $HAs]
              as %n %err ⟨%k, Hs8s, HWr, %Hk, #Herr⟩
            (try wp_auto)
            have Hxs : ((u64Le (W64 (pbEnc raftpb.Entry.ty p).length)).reverse).length = 8 := by
              simp [u64Le_length]
            cases err with
            | ok ei =>
              wp_auto
              wp_for_post
              iapply HΦ
              isplitr
              · first | iapply http.errStrOk_nil | iassumption
              iexists _, ⟨cst.term, cst.index + W64 j⟩
              iframe HWr
              isplitl
              · iunfold v2EncOwn
                iexists buf, s8, s1, zs', (u64Le (W64 (pbEnc raftpb.Entry.ty p).length)).reverse, [W8 1]
                iframe; iframe #; iframe %
              iintro %h0; cases h0
            | nil =>
            have hk : k = 8 := by
              have := Hk.2.2 rfl; simpa [List.length_reverse, u64Le_length] using this
            subst hk
            rw [List.take_of_length_le (l := (u64Le (W64 (pbEnc raftpb.Entry.ty p).length)).reverse)
              (by simp [List.length_reverse, u64Le_length])]
            wp_auto
            wp_if_destruct
            · -- small: marshalled into the encoder's buffer
              (try wp_auto)
              ihave %Hbwf := ownSliceCap_wf _ _ $$ Hbufc
              have h0 : sint.Z (W64 0) = 0 := rfl
              rw [if_pos (by simp only [h0]; omega)]
              ihave ⟨-, Hb0, Hb0c⟩ := ownSlice_slice_with_cap (V := w8) (W64 0) (W64 0) buf zs'
                (by simp only [h0]; omega) $$ [$Hbufs $Hbufc]
              rw [show subslice (sint.nat (W64 0)) (sint.nat (W64 0)) zs' = [] by simp [subslice]]
              (try wp_auto)
              rw [if_pos (by rw [hjz]; omega)]
              wp_apply (wp_load_slice_index (V := Loc) es _ els DFrac.discard p (by rw [hjz]; omega))
                $$ [Hes] as Hes
              · iframe; iframe #; ipureintro; rw [hjz]; exact Hp
              (try wp_auto)
              have hme : (pbEntry (GF := GF)).marshals e := trivial
              have wpMA := wp_MarshalAppend pbEntry opts_ptr (DFrac.own 1) p e
                (slice.slice buf w8 (W64 0) (W64 0)) [] hme
              simp only [pbEntry_ty, pbEntry_ro, pbEntry_wire, List.nil_append] at wpMA
              wp_apply wpMA $$ [$opts $Hb0 $Hb0c] as %b' ⟨opts, Hb', Hb'c, %Hb'⟩
              · iexact Hep
              (try wp_auto)
              ihave #HAe : □ A (h ++ [W8 1] ++ (u64Le (W64 st.ents.length)).reverse ++
                  entFrames ((els.map (pbEnc raftpb.Entry.ty)).take j) ++
                  (u64Le (W64 (pbEnc raftpb.Entry.ty p).length)).reverse ++ pbEnc raftpb.Entry.ty p) $$ []
              · imodintro
                ihave H := HAp $$ %([W8 1] ++ (u64Le (W64 st.ents.length)).reverse ++
                  entFrames ((els.map (pbEnc raftpb.Entry.ty)).take j) ++
                  (u64Le (W64 (pbEnc raftpb.Entry.ty p).length)).reverse ++ pbEnc raftpb.Entry.ty p) %(by
                    rw [hEj, hEl]
                    exact ⟨entFrames ((els.map (pbEnc raftpb.Entry.ty)).drop (j + 1)) ++
                      u64Be st.msg.Commit', by simp [u64Be, List.append_assoc]⟩)
                simp only [List.append_assoc] at *
                iexact H
              wp_apply Hwr $$ %b' %(DFrac.own 1) %(pbEnc raftpb.Entry.ty p)
                %(h ++ [W8 1] ++ (u64Le (W64 st.ents.length)).reverse ++
                  entFrames ((els.map (pbEnc raftpb.Entry.ty)).take j) ++
                  (u64Le (W64 (pbEnc raftpb.Entry.ty p).length)).reverse) [$Hb' $HWr $HAe]
                as %n2 %err2 ⟨%k2, Hb', HWr, %Hk2, #Herr⟩
              -- the buffer back: `MarshalAppend` wrote within it
              have hsmall : (pbEnc raftpb.Entry.ty p).length < 1048576 := by
                have : sint.Z (W64 1048576) = 1048576 := by word
                have : sint.Z (W64 (pbEnc raftpb.Entry.ty p).length) =
                  (pbEnc raftpb.Entry.ty p).length := by word
                omega
              have hcapge : (pbEnc raftpb.Entry.ty p).length ≤
                  uint.nat (slice.slice buf w8 (W64 0) (W64 0)).cap := by
                simp only [slice.slice]
                exact uint_nat_ge_of_sint (by unfold v2BufSize at Hbuflen; omega)
              obtain ⟨hptr, hcap⟩ := Hb'.2 hcapge
              ihave %Hb'l := ownSlice_len _ _ _ $$ Hb'
              ihave ⟨%vs, -, Hbufs, Hbufc⟩ := ownSlice_slice_into_capacity (V := w8) (W64 0) buf.len b'
                (pbEnc raftpb.Entry.ty p) $$ [$Hb' $Hb'c]
              · ipureintro
                simp only [hcap, slice.slice, h0]
                unfold v2BufSize at Hbuflen
                refine ⟨Int.le_refl _, by omega, by word, by word⟩
              rw [slice_back hptr hcap]
              (try wp_auto)
              cases err2 with
              | ok ei =>
                wp_auto
                wp_for_post
                iapply HΦ
                isplitr
                · first | iapply http.errStrOk_nil | iassumption
                iexists _, ⟨cst.term, cst.index + W64 j⟩
                iframe HWr
                isplitl
                · iunfold v2EncOwn
                  iexists buf, s8, s1, (pbEnc raftpb.Entry.ty p ++ vs).drop (sint.nat (W64 0)),
                    (u64Le (W64 (pbEnc raftpb.Entry.ty p).length)).reverse, [W8 1]
                  iframe; iframe #; iframe %
                iintro %h0; cases h0
              | nil =>
              have hk2 : k2 = (pbEnc raftpb.Entry.ty p).length := Hk2.2.2 rfl
              subst hk2
              rw [List.take_of_length_le (l := pbEnc raftpb.Entry.ty p) (Nat.le_refl _)]
              wp_auto
              wp_for_post
              iframe
              iexists (j + 1), _, _
              rw [show W64 ((j + 1 : Nat) : Int) = W64 j + W64 1 by word,
                show cst.index + (W64 j + W64 1) = cst.index + W64 j + W64 1 by word,
                entFrames_take_succ _ j (by simp [Hel]; omega), HEj]
              simp only [u64Be, List.append_assoc] at *
              iframe
              ipureintro
              exact ⟨Hxs, by omega⟩
            · -- large: marshalled into a fresh slice
              (try wp_auto)
              rw [if_pos (by rw [hjz]; omega)]
              wp_apply (wp_load_slice_index (V := Loc) es _ els DFrac.discard p (by rw [hjz]; omega))
                $$ [Hes] as Hes
              · iframe; iframe #; ipureintro; rw [hjz]; exact Hp
              (try wp_auto)
              have hme : (pbEntry (GF := GF)).marshals e := trivial
              have wpMM := wp_MustMarshalMessage pbEntry p e hme
              simp only [pbEntry_ty, pbEntry_ro, pbEntry_wire] at wpMM
              wp_apply wpMM $$ [] as %d ⟨Hd, -, -⟩
              · iexact Hep
              (try wp_auto)
              ihave #HAe : □ A (h ++ [W8 1] ++ (u64Le (W64 st.ents.length)).reverse ++
                  entFrames ((els.map (pbEnc raftpb.Entry.ty)).take j) ++
                  (u64Le (W64 (pbEnc raftpb.Entry.ty p).length)).reverse ++ pbEnc raftpb.Entry.ty p) $$ []
              · imodintro
                ihave H := HAp $$ %([W8 1] ++ (u64Le (W64 st.ents.length)).reverse ++
                  entFrames ((els.map (pbEnc raftpb.Entry.ty)).take j) ++
                  (u64Le (W64 (pbEnc raftpb.Entry.ty p).length)).reverse ++ pbEnc raftpb.Entry.ty p) %(by
                    rw [hEj, hEl]
                    exact ⟨entFrames ((els.map (pbEnc raftpb.Entry.ty)).drop (j + 1)) ++
                      u64Be st.msg.Commit', by simp [u64Be, List.append_assoc]⟩)
                simp only [List.append_assoc] at *
                iexact H
              wp_apply Hwr $$ %d %(DFrac.own 1) %(pbEnc raftpb.Entry.ty p)
                %(h ++ [W8 1] ++ (u64Le (W64 st.ents.length)).reverse ++
                  entFrames ((els.map (pbEnc raftpb.Entry.ty)).take j) ++
                  (u64Le (W64 (pbEnc raftpb.Entry.ty p).length)).reverse) [$Hd $HWr $HAe]
                as %n2 %err2 ⟨%k2, -, HWr, %Hk2, #Herr⟩
              (try wp_auto)
              cases err2 with
              | ok ei =>
                wp_auto
                wp_for_post
                iapply HΦ
                isplitr
                · first | iapply http.errStrOk_nil | iassumption
                iexists _, ⟨cst.term, cst.index + W64 j⟩
                iframe HWr
                isplitl
                · iunfold v2EncOwn
                  iexists buf, s8, s1, zs',
                    (u64Le (W64 (pbEnc raftpb.Entry.ty p).length)).reverse, [W8 1]
                  iframe; iframe #; iframe %
                iintro %h0; cases h0
              | nil =>
              have hk2 : k2 = (pbEnc raftpb.Entry.ty p).length := Hk2.2.2 rfl
              subst hk2
              rw [List.take_of_length_le (l := pbEnc raftpb.Entry.ty p) (Nat.le_refl _)]
              wp_auto
              wp_for_post
              iframe
              iexists (j + 1), _, _
              rw [show W64 ((j + 1 : Nat) : Int) = W64 j + W64 1 by word,
                show cst.index + (W64 j + W64 1) = cst.index + W64 j + W64 1 by word,
                entFrames_take_succ _ j (by simp [Hel]; omega), HEj]
              simp only [u64Be, List.append_assoc] at *
              iframe
              ipureintro
              exact ⟨Hxs, by omega⟩
          · -- all entries written: the commit index
            have hjn : j = st.ents.length := by
              have : sint.Z (W64 (j : Int)) = j := by word
              omega
            subst hjn
            rw [List.take_of_length_le (by simp [Hel])]
            wp_apply wp_GetCommit.1 ml DFrac.discard DFrac.discard false st $$ [] as -
            · iexact Hm
            (try wp_auto)
            wp_apply encoding.binary.wp_BigEndian_PutUint64 s8 x8' [] st.msg.Commit' Hx8' $$ [Hs8s]
              as Hs8s
            · simp only [List.append_nil]; iexact Hs8s
            simp only [List.append_nil]
            (try wp_auto)
            ihave #HAc : □ A (h ++ [W8 1] ++ (u64Le (W64 st.ents.length)).reverse ++
                entFrames (els.map (pbEnc raftpb.Entry.ty)) ++ (u64Le st.msg.Commit').reverse) $$ []
            · imodintro
              ihave H := HAp $$ %_ %(List.prefix_refl _)
              simp only [shortBytes, hEl, u64Be, List.append_assoc, List.cons_append,
                List.nil_append] at *
              iexact H
            wp_apply Hwr $$ %s8 %(DFrac.own 1) %((u64Le st.msg.Commit').reverse)
              %(h ++ [W8 1] ++ (u64Le (W64 st.ents.length)).reverse ++
                entFrames (els.map (pbEnc raftpb.Entry.ty))) [$Hs8s $HWr $HAc]
              as %n %err ⟨%k, Hs8s, HWr, %Hk, #Herr⟩
            (try wp_auto)
            have Hxc : ((u64Le st.msg.Commit').reverse).length = 8 := by simp [u64Le_length]
            cases err with
            | ok ei =>
              wp_auto
              iapply HΦ
              isplitr
              · first | iapply http.errStrOk_nil | iassumption
              iexists _, ⟨cst.term, cst.index + W64 st.ents.length⟩
              iframe HWr
              isplitl
              · iunfold v2EncOwn
                iexists buf, s8, s1, zs', (u64Le st.msg.Commit').reverse, [W8 1]
                iframe; iframe #; iframe %
              iintro %h0; cases h0
            | nil =>
            have hk : k = 8 := by have := Hk.2.2 rfl; simpa [u64Le_length] using this
            subst hk
            rw [List.take_of_length_le (by simp [u64Le_length])]
            wp_auto
            wp_apply wp_Since as %d -
            (try wp_auto)
            wp_apply wp_Succ fs d $$ []
            · ipureintro; exact Hfsnn
            (try wp_auto)
            iapply HΦ
            isplitr
            · first | iapply http.errStrOk_nil | iassumption
            iexists _, ⟨cst.term, cst.index + W64 st.ents.length⟩
            iframe HWr
            isplitl
            · iunfold v2EncOwn
              iexists buf, s8, s1, zs', (u64Le st.msg.Commit').reverse, [W8 1]
              iframe; iframe #; iframe %
            iintro -
            ipureintro
            refine ⟨_, Hfr, ?_⟩
            simp [shortBytes, hEl, u64Be, List.append_assoc]
        · rw [decide_eq_false (p := st.msg.LogTerm' = st.msg.Term') c3]
          wp_auto
          enc_full
      · rw [decide_eq_false (p := cst.term = st.msg.LogTerm') c2]
        wp_auto
        enc_full
    · rw [decide_eq_false (p := cst.index = st.msg.Index') c1]
      wp_auto
      enc_full

end proof

end EtcdGrove
end Perennial

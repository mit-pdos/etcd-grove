/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/raftNode__processMessages.lean`. Lean-first (no
Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.raftNode__processMessages
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetTo
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetType
public import Spec.go_uber_org.zap.String
public import Spec.go_uber_org.zap.Duration
public import Spec.go_uber_org.zap.Logger__Warn
public import Perennial.Proof.fmt

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- (D22 S-l sender) A `Ready`'s message opened: its fields at some fraction, and back to what
it is for the transport (any but a `MsgSnap`) or for `msgSnapC` (a `MsgSnap`). -/
theorem rnMsgR_open (E : RNEnv GF) (γ : RNNames) (m : Loc) :
    rnMsgR E γ m ⊢ ∃ (dq : DFrac) (st : MsgSt), msgOwn m dq st ∗
      ((⌜st.msg.Type' ≠ MsgSnap⌝ -∗ msgOwn m dq st -∗ rnMsgOk E m) ∧
       (⌜st.msg.Type' = MsgSnap⌝ -∗ msgOwn m dq st -∗ rnSnapMsg γ m)) := by
  -- SNAPSHOT-SORRY (to keep, when the rest is proved): the `MsgSnap` side: `rnSnapMsg`'s `sentMsg`/`msgCredits` kept
  sorry
/- REPAIR-OLD
  iintro H
  iunfold rnMsgR at H
  icases H with (⟨%to, %ty, #Hat, %Hty, HM⟩ | Hs)
  · iunfold msgAt at Hat
    icases Hat with ⟨%st, #Hm, %Hst⟩
    obtain ⟨rfl, rfl⟩ := Hst
    iexists DFrac.discard, st
    iframe Hm
    isplit
    · iintro %_ -
      iunfold rnMsgOk
      iexists st.msg.To', st.msg.Type'
      iframe HM
      iunfold msgAt
      iexists st
      iframe Hm
      ipureintro; exact ⟨rfl, rfl⟩
    · iintro %h
      exact absurd h Hty
  · iunfold rnSnapMsg at Hs
    iexfalso; iexact Hs
-/

/-- `m.GetTo()` at any fraction. -/
theorem wp_msgOwn_GetTo (wp_GetTo : raftpb.Message.GetTo.spec (GF := GF) (hG := hG))
    (m : Loc) (dq : DFrac) (st : MsgSt) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb ∗ msgOwn m dq st }}
      (App (Val (m @!! go.GoType.PointerType raftpb.Message.ty @!! go!"GetTo")) (Val #()))
    {{ RET #st.msg.To'; msgOwn m dq st }} := by
  iintro %Φ ⟨#Hi, Hm⟩ HΦ
  iapply wp_GetTo.1 m dq DFrac.discard false st $$ [$Hi $Hm]
  inext
  iexact HΦ

/-- `m.GetType()` at any fraction. -/
theorem wp_msgOwn_GetType (wp_GetType : raftpb.Message.GetType.spec (GF := GF) (hG := hG))
    (m : Loc) (dq : DFrac) (st : MsgSt) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb ∗ msgOwn m dq st }}
      (App (Val (m @!! go.GoType.PointerType raftpb.Message.ty @!! go!"GetType")) (Val #()))
    {{ RET #st.msg.Type'; msgOwn m dq st }} := by
  iintro %Φ ⟨#Hi, Hm⟩ HΦ
  iapply wp_GetType.1 m dq DFrac.discard false st $$ [$Hi $Hm]
  inext
  iexact HΦ

theorem wp_msgOwn_GetTo' (wp_GetTo : raftpb.Message.GetTo.spec (GF := GF) (hG := hG))
    (m : Loc) (dq : DFrac) (st : MsgSt) (to : w64) (h : st.msg.To' = to) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb ∗ msgOwn m dq st }}
      (App (Val (m @!! go.GoType.PointerType raftpb.Message.ty @!! go!"GetTo")) (Val #()))
    {{ RET #to; msgOwn m dq st }} := by
  subst h; exact wp_msgOwn_GetTo wp_GetTo m dq st

theorem wp_msgOwn_GetType' (wp_GetType : raftpb.Message.GetType.spec (GF := GF) (hG := hG))
    (m : Loc) (dq : DFrac) (st : MsgSt) (ty : w32) (h : st.msg.Type' = ty) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb ∗ msgOwn m dq st }}
      (App (Val (m @!! go.GoType.PointerType raftpb.Message.ty @!! go!"GetType")) (Val #()))
    {{ RET #ty; msgOwn m dq st }} := by
  subst h; exact wp_msgOwn_GetType wp_GetType m dq st

theorem raftNode.processMessages.wp_proof
    (wp_GetTo : raftpb.Message.GetTo.spec (GF := GF) (hG := hG))
    (wp_GetType : raftpb.Message.GetType.spec (GF := GF) (hG := hG))
    (wp_String : zap.String.spec (GF := GF) (hG := hG))
    (wp_Duration : zap.Duration.spec (GF := GF) (hG := hG))
    (wp_Warn : zap.Logger.Warn.spec (GF := GF) (hG := hG)) :
    raftNode.processMessages.spec (GF := GF) (hG := hG) := by
  -- SNAPSHOT-SORRY (to keep, when the rest is proved): the `MsgSnap` arm (raft.go:373-383): `msgSnapC`'s bag takes `rnSnapMsg γ m`, or it is dropped when full
  sorry
/- REPAIR-OLD
  have wp_GetTo := wp_msgOwn_GetTo' wp_GetTo
  have wp_GetType := wp_msgOwn_GetType' wp_GetType
  intro E γ r sl msL
  wp_start as ⟨#Hr, #Hsl, Hall⟩
  ihave %Hlen := ownSlice_len _ _ _ $$ Hsl
  ihave #Hr' := Hr
  iunfold isRaftNode at Hr'
  iNamed Hr'
  wp_auto
  ihave IH : iprop(∃ (k : w64) (out : GoSlice) (outL : List Loc) (b : Bool),
      "r" ∷ r_ptr ↦ r ∗ "ms" ∷ ms_ptr ↦ sl ∗ "i" ∷ i_ptr ↦ k ∗
      "messages" ∷ messages_ptr ↦ out ∗ "Hout" ∷ out ↦* outL ∗
      "Hcap" ∷ ownSliceCap Loc out (DFrac.own 1) ∗ "Houtok" ∷ ([∗list] m ∈ outL, rnMsgOk E m) ∗
      "sentAppResp" ∷ sentAppResp_ptr ↦ b ∗
      -- (D21 stage M1) the messages not yet looked at, each with its bundle
      "Hall" ∷ ([∗list] m ∈ msL.take (sint.Z k + 1).toNat, rnMsgR E γ m) ∗
      "%Hk" ∷ ⌜-1 ≤ sint.Z k ∧ sint.Z k < sint.Z sl.len⌝) $$ [r ms i messages sentAppResp Hall]
  · iexists sl.len - W64 1, slice.nil, [], false
    iframe r ms i sentAppResp
    rw [List.take_of_length_le (by rw [Hlen.1]; word)]
    iframe Hall
    isplitl [messages]
    · iexact messages
    isplitr
    · iapply ownSlice_nil
    isplitr
    · iapply ownSliceCap_nil
    isplitr
    · iapply BigSepL.bigSepL_nil.2; iempintro
    ipureintro; constructor <;> word
  ihave #Hrpb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb $$ []
  · iPkgInit
  wp_for IH
  wp_if_destruct
  · have hk0 : 0 ≤ sint.Z k := by word
    have hkl : (sint.Z k).toNat < msL.length := by rw [Hlen.1]; word
    obtain ⟨m, hm⟩ : ∃ m, msL[(sint.Z k).toNat]? = some m :=
      ⟨_, List.getElem?_eq_getElem hkl⟩
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by word, by word⟩)]
    wp_apply wp_load_slice_index sl (sint.Z k) msL DFrac.discard m (by word) $$ [] as -
    · iframe Hsl; ipureintro; exact hm
    -- (D21 stage M1) the message's bundle, taken from the ones not yet looked at
    have htake : msL.take (sint.Z k + 1).toNat = msL.take (sint.Z k).toNat ++ [m] := by
      rw [show (sint.Z k + 1).toNat = (sint.Z k).toNat + 1 by omega, List.take_succ, hm]; rfl
    have hk1 : (sint.Z (k - W64 1) + 1).toNat = (sint.Z k).toNat := by
      have : sint.Z (k - W64 1) = sint.Z k - 1 := by word
      omega
    rw [htake]
    icases (BigSepL.bigSepL_snoc (Φ := fun _ m => rnMsgR (GF := GF) E γ m)).1 $$ Hall
      with ⟨Hall, HmR⟩
    -- (D22 S-l sender) a `MsgSnap` owned, any other read-only
    icases rnMsgR_open E γ m $$ HmR with ⟨%dq, %st, Hmat, HK⟩
    obtain ⟨to, hto⟩ : ∃ to, st.msg.To' = to := ⟨_, rfl⟩
    obtain ⟨ty, hty⟩ : ∃ ty, st.msg.Type' = ty := ⟨_, rfl⟩
    wp_apply wp_GetTo m dq st to hto $$ [$Hrpb $Hmat] as Hmat
    iunfold isRNIDRemoved at Hidri
    ispecialize Hidri $$ %to
    wp_apply Hidri as %rm -
    wp_if_destruct
    rotate_left
    · -- removed member: `continue`
      wp_for_post
      iframe HΦ «$res0»
      iexists k - W64 1, out, outL, b
      rw [hk1]
      iframe
      ipureintro; constructor <;> word
    wp_apply wp_GetType m dq st _ hty $$ [$Hrpb $Hmat] as Hmat
    wp_if_destruct
    · -- `MsgAppResp`: only the last one
      cases b
      rotate_left
      · wp_auto
        wp_for_post
        iframe HΦ «$res0»
        iexists k - W64 1, out, outL, true
        rw [hk1]
        iframe
        ipureintro; constructor <;> word
      wp_auto
      wp_apply wp_GetType m dq st _ hty $$ [$Hrpb $Hmat] as Hmat
      wp_apply wp_GetType m dq st _ hty $$ [$Hrpb $Hmat] as Hmat
      wp_apply wp_slice_literal (l := [m])
      isplitr
      · ipureintro; rfl
      iintro %msl ⟨Hmsl, -⟩
      wp_apply wp_slice_append out outL _ [m] (DFrac.own 1) $$ [$Hout $Hcap $Hmsl]
        as %out' ⟨Hout, Hcap, -⟩
      wp_for_post
      iframe HΦ «$res0»
      iexists k - W64 1, out', outL ++ [m], _
      rw [hk1]
      iframe r ms i messages Hout Hcap sentAppResp Hall
      have hne : st.msg.Type' ≠ MsgSnap := by
        rw [hty]; first | decide | (unfold MsgSnap; intro h; simp_all)
      icases HK with ⟨HK, -⟩
      ihave HmOk := HK $$ %hne Hmat
      isplitl [Houtok HmOk]

      · iapply BigSepL.bigSepL_snoc.2
        iframe Houtok HmOk
      ipureintro; constructor <;> word
    · wp_apply wp_GetType m dq st _ hty $$ [$Hrpb $Hmat] as Hmat
      wp_if_destruct
      · -- `MsgSnap`: to `msgSnapC` if it has room, then `continue`
        -- (D19p) handed on with its type
        -- (D22 S-l sender) owned, with its protocol facts
        have hsn : st.msg.Type' = MsgSnap := hty
        icases HK with ⟨-, HK⟩
        ihave HmS : rnSnapMsg m $$ [HK Hmat]
        · iapply HK $$ %hsn Hmat
        iunfold isRNMsgSnapC at Hmsci
        icases Hmsci with ⟨%γc, #Hbag⟩
        ihave #Hbagch := is_bag_is_chan γc msc
          rnSnapMsg $$ Hbag
        rw [isChanBag_unseal]
        iunfold isChanBagDef at Hbag
        icases Hbag with ⟨#Hch, #Hinv⟩
        wp_apply_core chan.wp_select_nonblocking
        isplit
        · iapply BigAndL.bigAndL_cons.2
          isplit
          · simp only [chan.nonblockingClausePre]
            iexists Loc, inferInstance, inferInstance, inferInstance, inferInstance, msc, γc, m
            isplitr
            · ipureintro; exact ⟨rfl, rfl⟩
            isplitr
            · iexact Hbagch
            unfold nonblockingSendAu nonblockingSendAuInner
            isplit
            · iinv Hinv with Hi Hclose
              iapply fupd_mask_intro Std.LawfulSet.empty_subset
              iintro Hmask
              inext
              unfold chanBagInv
              icases Hi with ⟨%s, Hoc, Hi⟩
              iexists s
              iframe Hoc
              cases s with
              | RcvPending =>
                dsimp only
                iintro Hoc
                imod Hmask with -
                imod Hclose $$ [Hoc HmS] with -
                · inext; iexists .SndCommit m; iframe Hoc; dsimp only; iexact HmS
                imodintro
                wp_auto
                wp_for_post
                iframe HΦ «$res0»
                iexists k - W64 1, out, outL, _
                rw [hk1]
                iframe
                ipureintro; constructor <;> word
              | Buffered buff =>
                dsimp only
                iintro Hoc
                imod Hmask with -
                imod Hclose $$ [Hoc Hi HmS] with -
                · inext; iexists .Buffered (buff ++ [m]); iframe Hoc; dsimp only
                  iapply BigSepL.bigSepL_snoc.2; iframe Hi HmS
                imodintro
                wp_auto
                wp_for_post
                iframe HΦ «$res0»
                iexists k - W64 1, out, outL, _
                rw [hk1]
                iframe
                ipureintro; constructor <;> word
              | Closed d =>
                dsimp only
                iexfalso; iexact Hi
              | _ => dsimp only; itrivial
            · itrivial
          iapply BigAndL.bigAndL_nil.2
          itrivial
        · -- `default`: dropped
          wp_auto
          wp_for_post
          iframe HΦ «$res0»
          iexists k - W64 1, out, outL, _
          rw [hk1]
          iframe
          ipureintro; constructor <;> word

      wp_apply wp_GetType m dq st _ hty $$ [$Hrpb $Hmat] as Hmat
      wp_if_destruct
      · -- `MsgHeartbeat`: the timeout detector
        wp_apply wp_GetTo m dq st _ hto $$ [$Hrpb $Hmat] as Hmat
        iunfold isRNTimeoutDetector at Htdi
        icases Htdi with ⟨%Htdnn, #HReset, #HObs⟩
        ispecialize HObs $$ %to
        wp_apply HObs as %ok %d -
        cases ok
        · -- late: the warning and the counter
          wp_auto
          ihave #Hfmt : isPkgInit (PROP := IProp GF) pkg_id.fmt $$ []
          · iPkgInit
          ihave #Hzap : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
          · iPkgInit
          wp_apply wp_GetTo m dq st _ hto $$ [$Hrpb $Hmat] as Hmat
          wp_apply wp_slice_literal
          isplitr
          · ipureintro; rfl
          iintro %asl ⟨Hasl, -⟩
          wp_apply _root_.Perennial.fmt.wp_Sprintf _ _ _ (DFrac.own 1)
            (_root_.Perennial.fmt.ArgsWf.cons_int _ _ _ (_root_.Perennial.fmt.IntArgValue.uint64 to)
              _root_.Perennial.fmt.ArgsWf.nil) $$ [$Hfmt $Hasl] as %str -
          wp_apply wp_String _ _ $$ [$Hzap] as %f0 -
          wp_apply wp_Duration _ _ $$ [$Hzap] as %f1 -
          wp_apply wp_Duration _ _ $$ [$Hzap] as %f2 -
          wp_apply wp_Duration _ _ $$ [$Hzap] as %f3 -
          wp_apply wp_slice_literal
          isplitr
          · ipureintro; rfl
          iintro %fsl -
          wp_auto
          wp_apply wp_Warn lg _ _ $$ [$Hzap]
          · ipureintro; exact Hlgnn
          ihave Hsi : (srvInit : IProp GF) $$ []
          · iapply isPkgInit_access $$ Hpkg
          iunfold srvInit at Hsi
          icases Hsi with ⟨⟨-, -, -, -, ⟨%c, #Hc, #Hcs⟩, -⟩, -⟩
          iunfold go_etcd_io.etcd.server.v3.storage.mvcc.counterSpec at Hcs
          icases Hcs with ⟨#HInc, -⟩
          wp_auto
          wp_apply HInc
          wp_apply wp_slice_literal (l := [m])
          isplitr
          · ipureintro; rfl
          iintro %msl ⟨Hmsl, -⟩
          wp_apply wp_slice_append out outL _ [m] (DFrac.own 1) $$ [$Hout $Hcap $Hmsl]
            as %out' ⟨Hout, Hcap, -⟩
          wp_for_post
          iframe HΦ «$res0»
          iexists k - W64 1, out', outL ++ [m], _
          rw [hk1]
          iframe r ms i messages Hout Hcap sentAppResp Hall
          have hne : st.msg.Type' ≠ MsgSnap := by
            rw [hty]; first | decide | (unfold MsgSnap; intro h; simp_all)
          icases HK with ⟨HK, -⟩
          ihave HmOk := HK $$ %hne Hmat
          isplitl [Houtok HmOk]
          · iapply BigSepL.bigSepL_snoc.2
            iframe Houtok HmOk
          ipureintro; constructor <;> word


        · wp_auto

          wp_apply wp_slice_literal (l := [m])
          isplitr
          · ipureintro; rfl
          iintro %msl ⟨Hmsl, -⟩
          wp_apply wp_slice_append out outL _ [m] (DFrac.own 1) $$ [$Hout $Hcap $Hmsl]
            as %out' ⟨Hout, Hcap, -⟩
          wp_for_post
          iframe HΦ «$res0»
          iexists k - W64 1, out', outL ++ [m], _
          rw [hk1]
          iframe r ms i messages Hout Hcap sentAppResp Hall
          have hne : st.msg.Type' ≠ MsgSnap := by
            rw [hty]; first | decide | (unfold MsgSnap; intro h; simp_all)
          icases HK with ⟨HK, -⟩
          ihave HmOk := HK $$ %hne Hmat
          isplitl [Houtok HmOk]
          · iapply BigSepL.bigSepL_snoc.2
            iframe Houtok HmOk
          ipureintro; constructor <;> word


      wp_apply wp_slice_literal (l := [m])
      isplitr
      · ipureintro; rfl
      iintro %msl ⟨Hmsl, -⟩
      wp_apply wp_slice_append out outL _ [m] (DFrac.own 1) $$ [$Hout $Hcap $Hmsl]
        as %out' ⟨Hout, Hcap, -⟩
      wp_for_post
      iframe HΦ «$res0»
      iexists k - W64 1, out', outL ++ [m], _
      rw [hk1]
      iframe r ms i messages Hout Hcap sentAppResp Hall
      have hne : st.msg.Type' ≠ MsgSnap := by
        rw [hty]; first | decide | (unfold MsgSnap; intro h; simp_all)
      icases HK with ⟨HK, -⟩
      ihave HmOk := HK $$ %hne Hmat
      isplitl [Houtok HmOk]
      · iapply BigSepL.bigSepL_snoc.2
        iframe Houtok HmOk
      ipureintro; constructor <;> word


  · iapply HΦ
    iexists outL
    iframe Hout Houtok
-/

end proof

end EtcdGrove
end Perennial

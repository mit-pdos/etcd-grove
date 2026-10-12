/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/raftNode__processMessages.lean`. Lean-first (no
Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.raftNode__processMessages
public import EtcdDeps.Spec.go_etcd_io.raft.v3.raftpb.Message__GetTo
public import EtcdDeps.Spec.go_etcd_io.raft.v3.raftpb.Message__GetType
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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

theorem raftNode.processMessages.wp_proof
    (wp_GetTo : raftpb.Message.GetTo.spec (GF := GF) (hG := hG))
    (wp_GetType : raftpb.Message.GetType.spec (GF := GF) (hG := hG))
    (wp_String : zap.String.spec (GF := GF) (hG := hG))
    (wp_Duration : zap.Duration.spec (GF := GF) (hG := hG))
    (wp_Warn : zap.Logger.Warn.spec (GF := GF) (hG := hG)) :
    raftNode.processMessages.spec (GF := GF) (hG := hG) := by
  intro E γ r sl msL
  wp_start as ⟨#Hr, #Hsl, #Hall⟩
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
      "%Hk" ∷ ⌜-1 ≤ sint.Z k ∧ sint.Z k < sint.Z sl.len⌝) $$ [r ms i messages sentAppResp]
  · iexists sl.len - W64 1, slice.nil, [], false
    iframe r ms i sentAppResp
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
    ihave #HmOk := (BigSepL.bigSepL_lookup (Φ := fun _ m => rnMsgOk E m) hm) $$ Hall
    ihave #Hm := HmOk
    iunfold rnMsgOk at Hm

    icases Hm with ⟨%to, %ty, #Hmat, #HM⟩
    wp_apply wp_GetTo m to ty $$ [$Hrpb $Hmat]
    iunfold isRNIDRemoved at Hidri
    ispecialize Hidri $$ %to
    wp_apply Hidri as %rm -
    wp_if_destruct
    rotate_left
    · -- removed member: `continue`
      wp_for_post
      iframe HΦ
      iexists k - W64 1, out, outL, b
      iframe
      ipureintro; constructor <;> word
    wp_apply wp_GetType m to ty $$ [$Hrpb $Hmat]
    wp_if_destruct
    · -- `MsgAppResp`: only the last one
      cases b
      rotate_left
      · wp_auto
        wp_for_post
        iframe HΦ
        iexists k - W64 1, out, outL, true
        iframe
        ipureintro; constructor <;> word
      wp_auto
      wp_apply wp_GetType m to _ $$ [$Hrpb $Hmat]
      wp_apply wp_GetType m to _ $$ [$Hrpb $Hmat]
      wp_apply wp_slice_literal (l := [m])
      isplitr
      · ipureintro; rfl
      iintro %msl ⟨Hmsl, -⟩
      wp_apply wp_slice_append out outL _ [m] (DFrac.own 1) $$ [$Hout $Hcap $Hmsl]
        as %out' ⟨Hout, Hcap, -⟩
      wp_for_post
      iframe HΦ
      iexists k - W64 1, out', outL ++ [m], _
      iframe r ms i messages Hout Hcap sentAppResp
      isplitl [Houtok]

      · iapply BigSepL.bigSepL_snoc.2
        iframe Houtok HmOk
      ipureintro; constructor <;> word
    · wp_apply wp_GetType m to ty $$ [$Hrpb $Hmat]
      wp_if_destruct
      · -- `MsgSnap`: to `msgSnapC` if it has room, then `continue`
        iunfold isRNMsgSnapC at Hmsci
        icases Hmsci with ⟨%γc, #Hbag⟩
        ihave #Hbagch := is_bag_is_chan γc msc (rnMsgOk E) $$ Hbag
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
                imod Hclose $$ [Hoc] with -
                · inext; iexists .SndCommit m; iframe Hoc; dsimp only; iexact HmOk
                imodintro
                wp_auto
                wp_for_post
                iframe HΦ
                iexists k - W64 1, out, outL, _
                iframe
                ipureintro; constructor <;> word
              | Buffered buff =>
                dsimp only
                iintro Hoc
                imod Hmask with -
                imod Hclose $$ [Hoc Hi] with -
                · inext; iexists .Buffered (buff ++ [m]); iframe Hoc; dsimp only
                  iapply BigSepL.bigSepL_snoc.2; iframe Hi HmOk
                imodintro
                wp_auto
                wp_for_post
                iframe HΦ
                iexists k - W64 1, out, outL, _
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
          iframe HΦ
          iexists k - W64 1, out, outL, _
          iframe
          ipureintro; constructor <;> word

      wp_apply wp_GetType m to ty $$ [$Hrpb $Hmat]
      wp_if_destruct
      · -- `MsgHeartbeat`: the timeout detector
        wp_apply wp_GetTo m to _ $$ [$Hrpb $Hmat]
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
          wp_apply wp_GetTo m to _ $$ [$Hrpb $Hmat]
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
          icases Hsi with ⟨-, -, -, -, ⟨%c, #Hc, #Hcs⟩⟩
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
          iframe HΦ
          iexists k - W64 1, out', outL ++ [m], _
          iframe r ms i messages Hout Hcap sentAppResp
          isplitl [Houtok]
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
          iframe HΦ
          iexists k - W64 1, out', outL ++ [m], _
          iframe r ms i messages Hout Hcap sentAppResp
          isplitl [Houtok]
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
      iframe HΦ
      iexists k - W64 1, out', outL ++ [m], _
      iframe r ms i messages Hout Hcap sentAppResp
      isplitl [Houtok]
      · iapply BigSepL.bigSepL_snoc.2
        iframe Houtok HmOk
      ipureintro; constructor <;> word


  · iapply HΦ
    iexists outL
    iframe Hout Houtok

end proof

end EtcdGrove
end Perennial

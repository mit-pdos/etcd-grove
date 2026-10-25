/-
Proof of `Spec/go_etcd_io/etcd/client/v3/lessor__KeepAlive.lean` (item 1, the client lease).
Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.lessor__KeepAlive
public import Spec.go_etcd_io.etcd.client.v3.lessor__keepAliveCtxCloser
public import Spec.go_etcd_io.etcd.client.v3.lessor__recvKeepAliveLoop
public import Spec.go_etcd_io.etcd.client.v3.lessor__deadlineLoop
public import Spec.context.WithValue

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

set_option maxHeartbeats 0 in
theorem lessor.KeepAlive.wp_proof
    (wp_WithValue : context.WithValue.spec (GF := GF) (hG := hG))
    (wp_closer : lessor.keepAliveCtxCloser.spec (GF := GF) (hG := hG))
    (wp_recvLoop : lessor.recvKeepAliveLoop.spec (GF := GF) (hG := hG))
    (wp_deadlineLoop : lessor.deadlineLoop.spec (GF := GF) (hG := hG)) :
    lessor.KeepAlive.spec (GF := GF) (hG := hG) := by
  intro l addr ctx cd id
  wp_start as ⟨#Hl, #Hstr, #Heof, #Hall, #Htg, #Hctx⟩
  ihave #Hl' := Hl
  iunfold lessorAt at Hl'
  icases Hl' with ⟨%dc, %γd, %sc, %scd, %lg, %d, %γr, #Hdc, #Hdcu, #Hsc, #Hscc, #Hlg, %Hlgnn, #Hd,
    #Hrem, #Hmu, #Honce⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  ihave #Hctxp : isPkgInit (PROP := IProp GF) pkg_id.context $$ []
  · iPkgInit
  ihave Hci : (go_etcd_io.etcd.cache.v3.clientv3Init : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hci with ⟨-, -, -, -, -, -, -, #Hchsz, -⟩
  wp_auto
  wp_apply chan.wp_make2 (V := Loc) (W64 16) $$ [] as %ch %γ ⟨#Hch, %Hcap, Hoc⟩
  · ipureintro; constructor <;> decide
  ihave Hoc' : ownChan γ Loc (.Buffered ([] : List Loc)) $$ [Hoc]
  · iExactEq Hoc
    rfl
  imod chanTok_alloc ch γ [] $$ Hch Hoc' with ⟨Htok, #Hany⟩
  (try wp_auto)
  wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, Hinv⟩
  iunfold lessorInv at Hinv
  icases Hinv with ⟨%mref, %mm, %stv, %scf, %e, Hkas, Hm, HM, Hstf, Hscf, #Hscok, Herrf, Hreg⟩
  (try wp_auto)
  wp_bind (App (Val (GoInstruction SelectStmt)) _)
  iapply chan.wp_select_nonblocking
  isplit
  · iapply BigAndL.bigAndL_cons.2
    isplit
    · simp only [chan.nonblockingClausePre]
      iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, dc, γd
      isplit
      · ipureintro; rfl
      isplit
      · iapply ownBroadcastChan_is_chan $$ Hdcu
      iapply blocking_rcv_implies_nonblocking
      iapply broadcast_chan_receive _ _ _ _ _ $$ Hdcu
      iintro -
      (try wp_auto)
      wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hkas Hm HM Hstf Hscf Herrf Hreg]
      · inext; unfold lessorInv; iexists mref, mm, stv, scf, e; iframe; iframe #
      (try wp_auto)
      wp_apply wp_chanTok_close ch $$ [$Htok]
      (try wp_auto)
      iapply HΦ
      ileft
      ipureintro
      intro h; cases h
    · iapply BigAndL.bigAndL_nil.2; itrivial
  · (try wp_auto)
    wp_apply wp_map_lookup2 _ _ mref mm id (DFrac.own 1) $$ [$Hm] as Hm
    ihave #Hctx2 : iprop(context.isContextDef ctx cd) $$ [Hctx]
    · iexact Hctx
    iunfold context.isContextDef at Hctx2
    icases Hctx2 with ⟨-, #HDoneC, -⟩
    (try wp_auto)
    wp_apply +noauto HDoneC as %ch1 %γ1 #Hdone1
    ihave #Hch1 := context.isContextDone_is_chan _ _ _ $$ Hdone1
    ihave %Hch1nn := isChan_not_null _ _ _ $$ Hch1
    (try wp_auto)
    rw [decide_eq_false (show ch1 ≠ chan.nil from Hch1nn)]
    (try wp_auto)
    wp_apply (wp_WithValue ctx ⟨go_etcd_io.etcd.client.v3.keepAliveCtxKey.ty,
        #(zero_val go_etcd_io.etcd.client.v3.keepAliveCtxKey)⟩ _) $$ []
      as %c ⟨%Hcnn, -, -, %c', %vs, %Hc, -, #Hic, -, -⟩
    · iframe #; ipureintro; right; right; right; right; left; rfl
    subst Hc
    ihave #Hctx' := Hic $$ %cd Hctx
    (try wp_auto)
    -- register the pair `(ch, c')` at `&ctx` (the variable is not written again)
    imod lessorReg_register ⊤ γr ctx_ptr ch (GoInterface.ok c') $$ [$Hreg $ctx] with ⟨Hreg, #Hkr, #ctx⟩
    rcases Hlk : mm !! id with _ | ka
    · simp only [Option.isSome_none, Bool.false_eq_true, decide_false, Bool.not_false]
      (try wp_auto)
      wp_apply wp_slice_literal (V := GoChan) [ch]
      isplitr
      · ipureintro; rfl
      iintro %chsl ⟨Hchsl, Hchscap⟩
      (try wp_auto)
      wp_apply wp_slice_literal (V := GoInterface) [GoInterface.ok c']
      isplitr
      · ipureintro; rfl
      iintro %ctxsl ⟨Hctxsl, Hctxscap⟩
      (try wp_auto)
      wp_apply time.wp_Now as %t1 -
      wp_apply time.Time.wp_Add as %t2 -
      (try wp_auto)
      wp_apply time.wp_Now as %t3 -
      (try wp_auto)
      wp_apply chan.wp_make1 (V := Unit) as %kd %γkd ⟨#Hkdc, %_, Hkdoc⟩
      imod alloc_broadcast_chan iprop(True) γkd kd $$ Hkdc Hkdoc with Hkpend
      ihave #Hkdu := ownBroadcastChan_Unknown _ _ _ _ $$ Hkpend
      (try wp_auto)
      iStructNamed «$r0»
      ipersist donec
      wp_apply wp_mapInsert $$ [$Hm] as Hm
      (try wp_auto)
      ihave Htoks : iprop([∗list] c ∈ [ch], chanTok (GF := GF) c) $$ [Htok]
      · iapply BigSepL.bigSepL_singleton.2; iexact Htok
      ihave #Hctxs1 : iprop([∗list] c ∈ [GoInterface.ok c'], kaCtxOk (GF := GF) c) $$ []
      · iapply BigSepL.bigSepL_singleton.2
        unfold kaCtxOk
        iexists c', _
        iframe #
        ipureintro; rfl
      ihave #Hpair1 := kaPaired_singleton γr ch (GoInterface.ok c') $$ Hkr
      wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hkas Hm HM Hstf Hscf Herrf Hreg chs Hchsl Hchscap ctxs
        Hctxsl Hctxscap deadline nextKeepAlive Hkpend Htoks]
      · inext
        unfold lessorInv
        iexists mref, _, stv, scf, e
        iframe
        iframe #
        iapply (BigSepM.bigSepM_insert (Φ := fun (_ : w64) (ka : Loc) => kaOwn (GF := GF) γr ka)
          (m := mm) Hlk).2
        iframe HM
        unfold kaOwn
        iexists _, _, [ch], [GoInterface.ok c'], _, _, kd, γkd
        iframe
        unfold kaDone
        iframe #
        ipureintro; rfl
      (try wp_auto)
      ihave #Hctx3 : iprop(context.isContextDef c' { cd with Values := vs }) $$ [Hctx']
      · iexact Hctx'
      iunfold context.isContextDef at Hctx3
      icases Hctx3 with ⟨-, #HDoneC', -⟩
      wp_apply +noauto HDoneC' as %ch2 %γ2 #Hdone2
      ihave #Hch2 := context.isContextDone_is_chan _ _ _ $$ Hdone2
      ihave %Hch2nn := isChan_not_null _ _ _ $$ Hch2
      (try wp_auto)
      rw [decide_eq_false (show ch2 ≠ chan.nil from Hch2nn)]
      (try wp_auto)
      wp_apply wp_fork $$ []
      · wp_apply wp_closer l addr c' _ id kd γkd $$ []
        · iframe #
        itrivial
      (try wp_auto)
      ipersist l
      wp_func_lits
      wp_apply sync.Once.wp_Do (lsF go!"firstKeepAliveOnce" l)
        (ownBroadcastChan dc γd iprop(True) .Pending) iprop(True) _ $$ []
      · iframe #
        iintro %Φ' !> HP HΦ'
        wp_auto
        wp_apply wp_fork $$ [HP]
        · wp_apply wp_recvLoop l addr dc γd $$ [HP] as %_ -
          · iframe #; iframe
          itrivial
        (try wp_auto)
        wp_apply wp_fork $$ []
        · wp_apply wp_deadlineLoop l addr $$ []
          · iframe #
          itrivial
        (try wp_auto)
        iapply HΦ'; itrivial
      (try wp_auto)
      iapply HΦ
      iright
      isplitr
      · ipureintro; rfl
      iexists γ
      iexact Hany
    · simp only [Option.isSome_some, _root_.decide_true, Bool.not_true, Option.getD_some]
      icases (BigSepM.bigSepM_lookup_acc (Φ := fun (_ : w64) (ka : Loc) => kaOwn (GF := GF) γr ka)
        (m := mm) Hlk).1 $$ HM with ⟨Hka, HMback⟩
      iunfold kaOwn at Hka
      icases Hka with ⟨%chsS, %ctxsS, %chs, %ctxs, %dl, %nk, %kd', %γkd', Hchs, Hchsl, Hchscap,
        Hctxs, Hctxsl, Hctxscap, %Hlen, Hdl, Hnk, #Hkd', Hpend, Htoks, #Hctxok, #Hpair⟩
      ihave #Hkd'2 := Hkd'
      iunfold kaDone at Hkd'2
      icases Hkd'2 with ⟨#Hkdf, #Hkdu⟩
      (try wp_auto)
      wp_apply wp_slice_literal (V := GoInterface) [GoInterface.ok c']
      isplitr
      · ipureintro; rfl
      iintro %sl1 ⟨Hsl1, -⟩
      (try wp_auto)
      wp_apply wp_slice_append $$ [Hctxsl Hctxscap Hsl1] as %ctxsS' ⟨Hctxsl, Hctxscap, -⟩
      · iframe
      (try wp_auto)
      wp_apply wp_slice_literal (V := GoChan) [ch]
      isplitr
      · ipureintro; rfl
      iintro %sl2 ⟨Hsl2, -⟩
      (try wp_auto)
      wp_apply wp_slice_append $$ [Hchsl Hchscap Hsl2] as %chsS' ⟨Hchsl, Hchscap, -⟩
      · iframe
      (try wp_auto)
      ihave Htoks' : iprop([∗list] c ∈ chs ++ [ch], chanTok (GF := GF) c) $$ [Htoks Htok]
      · iapply BigSepL.bigSepL_append.2
        iframe Htoks
        iapply BigSepL.bigSepL_singleton.2; iexact Htok
      ihave #Hctxok' : iprop([∗list] c ∈ ctxs ++ [GoInterface.ok c'], kaCtxOk (GF := GF) c) $$ []
      · iapply BigSepL.bigSepL_append.2
        iframe #
        iapply BigSepL.bigSepL_singleton.2
        unfold kaCtxOk
        iexists c', _
        iframe #
        ipureintro; rfl
      ihave #Hpair' := kaPaired_snoc γr chs ctxs ch (GoInterface.ok c') Hlen $$ [$Hpair $Hkr]
      wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hkas Hm HMback Hstf Hscf Herrf Hreg Hchs Hchsl Hchscap
        Hctxs Hctxsl Hctxscap Hdl Hnk Hpend Htoks']
      · inext
        unfold lessorInv
        iexists mref, mm, stv, scf, e
        iframe
        iframe #
        iapply HMback
        unfold kaOwn
        iexists chsS', ctxsS', chs ++ [ch], ctxs ++ [GoInterface.ok c'], _, _, kd', γkd'
        iframe
        iframe #
        ipureintro; simp [Hlen]
      (try wp_auto)
      ihave #Hctx3 : iprop(context.isContextDef c' { cd with Values := vs }) $$ [Hctx']
      · iexact Hctx'
      iunfold context.isContextDef at Hctx3
      icases Hctx3 with ⟨-, #HDoneC', -⟩
      wp_apply +noauto HDoneC' as %ch2 %γ2 #Hdone2
      ihave #Hch2 := context.isContextDone_is_chan _ _ _ $$ Hdone2
      ihave %Hch2nn := isChan_not_null _ _ _ $$ Hch2
      (try wp_auto)
      rw [decide_eq_false (show ch2 ≠ chan.nil from Hch2nn)]
      (try wp_auto)
      wp_apply wp_fork $$ []
      · wp_apply wp_closer l addr c' _ id kd' γkd' $$ []
        · iframe #
        itrivial
      (try wp_auto)
      ipersist l
      wp_func_lits
      wp_apply sync.Once.wp_Do (lsF go!"firstKeepAliveOnce" l)
        (ownBroadcastChan dc γd iprop(True) .Pending) iprop(True) _ $$ []
      · iframe #
        iintro %Φ' !> HP HΦ'
        wp_auto
        wp_apply wp_fork $$ [HP]
        · wp_apply wp_recvLoop l addr dc γd $$ [HP] as %_ -
          · iframe #; iframe
          itrivial
        (try wp_auto)
        wp_apply wp_fork $$ []
        · wp_apply wp_deadlineLoop l addr $$ []
          · iframe #
          itrivial
        (try wp_auto)
        iapply HΦ'; itrivial
      (try wp_auto)
      iapply HΦ
      iright
      isplitr
      · ipureintro; rfl
      iexists γ
      iexact Hany

end proof

end EtcdGrove
end Perennial

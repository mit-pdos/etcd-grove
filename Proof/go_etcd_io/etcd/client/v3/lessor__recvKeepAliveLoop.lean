/-
Proof of `Spec/go_etcd_io/etcd/client/v3/lessor__recvKeepAliveLoop.lean` (item 1, the client lease).
Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.lessor__recvKeepAliveLoop
public import Spec.go_etcd_io.etcd.client.v3.lessor__resetRecv
public import Spec.go_etcd_io.etcd.client.v3.lessor__recvKeepAlive
public import Spec.go_etcd_io.etcd.client.v3.lessor__closeRequireLeader
public import Spec.go_etcd_io.etcd.client.v3.keepAlive__close
public import Spec.go_etcd_io.etcd.client.v3.canceledByCaller
public import Spec.go_etcd_io.etcd.client.v3.ContextError
public import Spec.errors.IsStatusErr
public import Spec.go_uber_org.zap.Error
public import Spec.go_uber_org.zap.Logger__Warn

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
theorem lessor.recvKeepAliveLoop.wp_proof
    (wp_resetRecv : lessor.resetRecv.spec (GF := GF) (hG := hG))
    (wp_recvKeepAlive : lessor.recvKeepAlive.spec (GF := GF) (hG := hG))
    (wp_closeRequireLeader : lessor.closeRequireLeader.spec (GF := GF) (hG := hG))
    (wp_close : keepAlive.close.spec (GF := GF) (hG := hG))
    (wp_canceledByCaller : canceledByCaller.spec (GF := GF) (hG := hG))
    (wp_ContextError : ContextError.spec (GF := GF) (hG := hG))
    (wp_Is : errors.IsStatusErr.spec (GF := GF) (hG := hG))
    (wp_Error : zap.Error.spec (GF := GF) (hG := hG))
    (wp_Warn : zap.Logger.Warn.spec (GF := GF) (hG := hG)) :
    lessor.recvKeepAliveLoop.spec (GF := GF) (hG := hG) := by
  intro l addr dc0 γd0
  wp_start as ⟨#Hl, #Hstr, #Heof, #Hall, #Htg, #Hdc0, Hpend⟩
  ihave #Hl' := Hl
  iunfold lessorAt at Hl'
  icases Hl' with ⟨%dc, %γd, %sc, %scd, %lg, %d, %γr, #Hdc, #Hdcu, #Hsc, #Hscc, #Hlg, %Hlgnn, #Hd,
    #Hrem, #Hmu, #Honce⟩
  icombine Hdc0 Hdc gives %Hdceq
  subst Hdceq
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  iunfold client.ctxErrClientAll at Hall
  ihave #Hsce := Hall $$ %sc %scd Hscc
  ihave #Hsce' := Hsce
  iunfold ctxErrClient at Hsce'
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  ipersist l
  ihave #Herrp : isPkgInit (PROP := IProp GF) pkg_id.errors $$ []
  · iPkgInit
  ihave #Hzap : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
  · iPkgInit
  wp_for
  wp_apply wp_resetRecv l addr $$ [] as %st %err Hres
  · iframe #
  (try wp_auto)
  icases Hres with (⟨%Herr, %γ, %Dn, %cd', #Hcs, HRt⟩ | ⟨%Hst, #Herr⟩)
  · subst Herr
    (try wp_auto)
    ihave #Hcs' := Hcs
    iunfold cliBidiStreamIs at Hcs'
    icases Hcs' with ⟨%ci, %Hci, -, #HRecv, -, -⟩
    subst Hci
    ihave IH : iprop(∃ L : List (w64 × w64),
        "HRt" ∷ cliRecvTok (Rep := pbLeaseKeepAliveResponse) γ L) $$ [HRt]
    · iexists []; iframe
    wp_for IH
    ihave #HR := HRecv $$ %L
    wp_apply HR $$ [$HRt] as %resp %rerr Hres
    (try wp_auto)
    icases Hres with (⟨%Herr, %m, #Hm, -, HRt⟩ | ⟨%Hresp, #Heofe, %Hne, HRt, -⟩ | ⟨%Hresp, #Hse0, HRt⟩)
    · subst Herr
      (try wp_auto)
      wp_apply wp_recvKeepAlive l addr resp m $$ []
      · iframe #
      (try wp_auto)
      wp_for_post
      iframe
      iexists _; iframe
    · iunfold client.eofOk at Heof
      ihave ⟨%Hce, #Hse⟩ := Heof $$ %rerr Heofe
      cases rerr with
      | nil => exact absurd rfl Hce.1
      | ok rei =>
        (try wp_auto)
        wp_apply wp_canceledByCaller sc scd _ $$ [] as %b -
        · iframe #
        cases b
        · (try wp_auto)
          wp_apply wp_ContextError sc scd (GoInterface.ok rei) $$ [] as %err' ⟨%Herr', #Hse'⟩
          · iframe #; ipureintro; exact fun _ => Hce.2
          (try wp_auto)
          ihave #Hrp : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.v3rpc.rpctypes $$ []
          · iPkgInit
          ihave ⟨%xnl, #Hnl⟩ := errNoLeader_of_init $$ Hrp
          (try wp_auto)
          wp_apply (wp_Is err' _ (Or.inl ⟨xnl, rfl⟩)) $$ [] as %bnl -
          · iframe #
          cases bnl
          · (try wp_auto)
            wp_for_post
            wp_apply +noauto time.wp_After as %tch %γt #Htch
            (try wp_auto)
            ihave #Hsc2 : iprop(context.isContextDef sc scd) $$ [Hscc]
            · iexact Hscc
            iunfold context.isContextDef at Hsc2
            icases Hsc2 with ⟨-, #HDoneS, -⟩
            wp_apply +noauto HDoneS as %chs %γs #Hdones
            wp_auto_lc 2
            wp_apply_core chan.wp_select_blocking
            iapply BigAndL.bigAndL_cons.2
            isplit
            · simp only [chan.blockingClausePre]
              iexists time.Time, inferInstance, inferInstance, inferInstance, inferInstance, tch, γt
              isplitr
              · ipureintro; rfl
              isplitr
              · iapply is_bag_is_chan $$ Htch
              iapply bag_recv_au $$ [$Hlc1 $Hlc2] Htch
              inext
              iintro %tm -
              (try wp_auto)
              wp_for_post
              iframe
            iapply BigAndL.bigAndL_cons.2
            isplit
            · simp only [chan.blockingClausePre]
              iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, chs, γs
              isplit
              · ipureintro; rfl
              isplit
              · iapply context.isContextDone_is_chan $$ Hdones
              iapply context.isContextDone_receive _ _ _ _ $$ Hdones
              iintro -
              (try wp_auto)
              ihave #HU := Hsce' $$ %Broadcast.Unknown
              wp_apply HU $$ [] as %e0 - %- -
              (try wp_auto)
              wp_for_post
              (try wp_auto)
              wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, Hinv⟩
              iunfold lessorInv at Hinv
              icases Hinv with ⟨%mref, %mm, %stv, %scf, %e, Hkas, Hm, HM, Hstf, Hscf, #Hscok, Herrf, Hreg⟩
              (try wp_auto)
              ihave #Htt : □ (True : IProp GF) $$ []
              · imodintro; itrivial
              wp_apply wp_broadcast_chan_close dc0 γd0 iprop(True) $$ [$Hpend $Htt] as -
              (try wp_auto)
              wp_func_lits
              wp_bind (App (App (Val (map.forRange _ _)) _) _)
              iapply wp_map_for_range (fun (keys : List w64) (i : Int) => iprop(∃ k0 : Loc,
                  "HM" ∷ ([∗map] k ↦ ka ∈ mm, ⌜k ∈ keys.take i.toNat⌝ ∨ kaOwn (GF := GF) γr ka) ∗
                  "ka" ∷ ka_ptr ↦ k0 ∗ "%Hi0" ∷ ⌜0 ≤ i⌝)) _ _ _ mref mm (DFrac.own 1) $$ Hm
              iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
              isplitl [HM ka]
              · iexists _
                simp only [named]
                iframe
                isplitl
                · iapply BigSepM.bigSepM_mono (fun _ => or_intro_r) $$ HM
                · ipureintro; omega
              isplitr
              · imodintro
                iintro %i %key %v ⟨%Hki, %Hmv⟩ HP
                iNamed HP
                (try wp_auto)
                icases (BigSepM.bigSepM_delete
                  (Φ := fun (k : w64) (ka : Loc) => iprop(⌜k ∈ keys.take i.toNat⌝ ∨ kaOwn (GF := GF) γr ka))
                  (m := mm) Hmv).1 $$ HM with ⟨Hka, HMr⟩
                icases Hka with (%Hin | Hka)
                · exfalso; exact not_mem_take_of_nodup Hknodup Hki Hin
                wp_apply wp_close γr v $$ [$Hka]
                (try wp_auto)
                unfold forMapPostcondition
                iright; ileft
                isplitr
                · ipureintro; rfl
                iexists _
                simp only [named]
                iframe
                isplitl
                · iapply (BigSepM.bigSepM_delete
                    (Φ := fun (k : w64) (ka : Loc) => iprop(⌜k ∈ keys.take (i + 1).toNat⌝ ∨ kaOwn (GF := GF) γr ka))
                    (m := mm) Hmv).2
                  isplitl []
                  · ileft; ipureintro
                    have := (mem_take_succ_iff Hki key).2 (Or.inr rfl)
                    rwa [show (i + 1).toNat = i.toNat + 1 by omega]
                  iapply BigSepM.bigSepM_mono (fun _ => or_mono (BI.pure_mono (fun h =>
                    List.take_subset_take_left _ (by omega) h)) .rfl) $$ HMr
                · ipureintro; omega
              · iintro HP Hm
                iNamed HP
                (try wp_auto)
                wp_apply wp_map_make1 (K := w64) (V := Loc) as %mref' Hm'
                (try wp_auto)
                wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hkas Hm' Hstf Hscf Herrf Hreg]
                · inext
                  unfold lessorInv
                  iexists mref', ∅, stv, scf, _
                  iframe
                  iframe #
                  iapply BigSepM.bigSepM_empty.2
                  itrivial
                (try wp_auto)
                iapply HΦ; itrivial
            iapply BigAndL.bigAndL_nil.2
            itrivial
          · (try wp_auto)
            wp_apply wp_closeRequireLeader l addr $$ []
            · iframe #
            (try wp_auto)
            wp_for_post
            wp_apply +noauto time.wp_After as %tch %γt #Htch
            (try wp_auto)
            ihave #Hsc2 : iprop(context.isContextDef sc scd) $$ [Hscc]
            · iexact Hscc
            iunfold context.isContextDef at Hsc2
            icases Hsc2 with ⟨-, #HDoneS, -⟩
            wp_apply +noauto HDoneS as %chs %γs #Hdones
            wp_auto_lc 2
            wp_apply_core chan.wp_select_blocking
            iapply BigAndL.bigAndL_cons.2
            isplit
            · simp only [chan.blockingClausePre]
              iexists time.Time, inferInstance, inferInstance, inferInstance, inferInstance, tch, γt
              isplitr
              · ipureintro; rfl
              isplitr
              · iapply is_bag_is_chan $$ Htch
              iapply bag_recv_au $$ [$Hlc1 $Hlc2] Htch
              inext
              iintro %tm -
              (try wp_auto)
              wp_for_post
              iframe
            iapply BigAndL.bigAndL_cons.2
            isplit
            · simp only [chan.blockingClausePre]
              iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, chs, γs
              isplit
              · ipureintro; rfl
              isplit
              · iapply context.isContextDone_is_chan $$ Hdones
              iapply context.isContextDone_receive _ _ _ _ $$ Hdones
              iintro -
              (try wp_auto)
              ihave #HU := Hsce' $$ %Broadcast.Unknown
              wp_apply HU $$ [] as %e0 - %- -
              (try wp_auto)
              wp_for_post
              (try wp_auto)
              wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, Hinv⟩
              iunfold lessorInv at Hinv
              icases Hinv with ⟨%mref, %mm, %stv, %scf, %e, Hkas, Hm, HM, Hstf, Hscf, #Hscok, Herrf, Hreg⟩
              (try wp_auto)
              ihave #Htt : □ (True : IProp GF) $$ []
              · imodintro; itrivial
              wp_apply wp_broadcast_chan_close dc0 γd0 iprop(True) $$ [$Hpend $Htt] as -
              (try wp_auto)
              wp_func_lits
              wp_bind (App (App (Val (map.forRange _ _)) _) _)
              iapply wp_map_for_range (fun (keys : List w64) (i : Int) => iprop(∃ k0 : Loc,
                  "HM" ∷ ([∗map] k ↦ ka ∈ mm, ⌜k ∈ keys.take i.toNat⌝ ∨ kaOwn (GF := GF) γr ka) ∗
                  "ka" ∷ ka_ptr ↦ k0 ∗ "%Hi0" ∷ ⌜0 ≤ i⌝)) _ _ _ mref mm (DFrac.own 1) $$ Hm
              iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
              isplitl [HM ka]
              · iexists _
                simp only [named]
                iframe
                isplitl
                · iapply BigSepM.bigSepM_mono (fun _ => or_intro_r) $$ HM
                · ipureintro; omega
              isplitr
              · imodintro
                iintro %i %key %v ⟨%Hki, %Hmv⟩ HP
                iNamed HP
                (try wp_auto)
                icases (BigSepM.bigSepM_delete
                  (Φ := fun (k : w64) (ka : Loc) => iprop(⌜k ∈ keys.take i.toNat⌝ ∨ kaOwn (GF := GF) γr ka))
                  (m := mm) Hmv).1 $$ HM with ⟨Hka, HMr⟩
                icases Hka with (%Hin | Hka)
                · exfalso; exact not_mem_take_of_nodup Hknodup Hki Hin
                wp_apply wp_close γr v $$ [$Hka]
                (try wp_auto)
                unfold forMapPostcondition
                iright; ileft
                isplitr
                · ipureintro; rfl
                iexists _
                simp only [named]
                iframe
                isplitl
                · iapply (BigSepM.bigSepM_delete
                    (Φ := fun (k : w64) (ka : Loc) => iprop(⌜k ∈ keys.take (i + 1).toNat⌝ ∨ kaOwn (GF := GF) γr ka))
                    (m := mm) Hmv).2
                  isplitl []
                  · ileft; ipureintro
                    have := (mem_take_succ_iff Hki key).2 (Or.inr rfl)
                    rwa [show (i + 1).toNat = i.toNat + 1 by omega]
                  iapply BigSepM.bigSepM_mono (fun _ => or_mono (BI.pure_mono (fun h =>
                    List.take_subset_take_left _ (by omega) h)) .rfl) $$ HMr
                · ipureintro; omega
              · iintro HP Hm
                iNamed HP
                (try wp_auto)
                wp_apply wp_map_make1 (K := w64) (V := Loc) as %mref' Hm'
                (try wp_auto)
                wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hkas Hm' Hstf Hscf Herrf Hreg]
                · inext
                  unfold lessorInv
                  iexists mref', ∅, stv, scf, _
                  iframe
                  iframe #
                  iapply BigSepM.bigSepM_empty.2
                  itrivial
                (try wp_auto)
                iapply HΦ; itrivial
            iapply BigAndL.bigAndL_nil.2
            itrivial
        · (try wp_auto)
          wp_for_post
          wp_for_post
          (try wp_auto)
          wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, Hinv⟩
          iunfold lessorInv at Hinv
          icases Hinv with ⟨%mref, %mm, %stv, %scf, %e, Hkas, Hm, HM, Hstf, Hscf, #Hscok, Herrf, Hreg⟩
          (try wp_auto)
          ihave #Htt : □ (True : IProp GF) $$ []
          · imodintro; itrivial
          wp_apply wp_broadcast_chan_close dc0 γd0 iprop(True) $$ [$Hpend $Htt] as -
          (try wp_auto)
          wp_func_lits
          wp_bind (App (App (Val (map.forRange _ _)) _) _)
          iapply wp_map_for_range (fun (keys : List w64) (i : Int) => iprop(∃ k0 : Loc,
              "HM" ∷ ([∗map] k ↦ ka ∈ mm, ⌜k ∈ keys.take i.toNat⌝ ∨ kaOwn (GF := GF) γr ka) ∗
              "ka" ∷ ka_ptr ↦ k0 ∗ "%Hi0" ∷ ⌜0 ≤ i⌝)) _ _ _ mref mm (DFrac.own 1) $$ Hm
          iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
          isplitl [HM ka]
          · iexists _
            simp only [named]
            iframe
            isplitl
            · iapply BigSepM.bigSepM_mono (fun _ => or_intro_r) $$ HM
            · ipureintro; omega
          isplitr
          · imodintro
            iintro %i %key %v ⟨%Hki, %Hmv⟩ HP
            iNamed HP
            (try wp_auto)
            icases (BigSepM.bigSepM_delete
              (Φ := fun (k : w64) (ka : Loc) => iprop(⌜k ∈ keys.take i.toNat⌝ ∨ kaOwn (GF := GF) γr ka))
              (m := mm) Hmv).1 $$ HM with ⟨Hka, HMr⟩
            icases Hka with (%Hin | Hka)
            · exfalso; exact not_mem_take_of_nodup Hknodup Hki Hin
            wp_apply wp_close γr v $$ [$Hka]
            (try wp_auto)
            unfold forMapPostcondition
            iright; ileft
            isplitr
            · ipureintro; rfl
            iexists _
            simp only [named]
            iframe
            isplitl
            · iapply (BigSepM.bigSepM_delete
                (Φ := fun (k : w64) (ka : Loc) => iprop(⌜k ∈ keys.take (i + 1).toNat⌝ ∨ kaOwn (GF := GF) γr ka))
                (m := mm) Hmv).2
              isplitl []
              · ileft; ipureintro
                have := (mem_take_succ_iff Hki key).2 (Or.inr rfl)
                rwa [show (i + 1).toNat = i.toNat + 1 by omega]
              iapply BigSepM.bigSepM_mono (fun _ => or_mono (BI.pure_mono (fun h =>
                List.take_subset_take_left _ (by omega) h)) .rfl) $$ HMr
            · ipureintro; omega
          · iintro HP Hm
            iNamed HP
            (try wp_auto)
            wp_apply wp_map_make1 (K := w64) (V := Loc) as %mref' Hm'
            (try wp_auto)
            wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hkas Hm' Hstf Hscf Herrf Hreg]
            · inext
              unfold lessorInv
              iexists mref', ∅, stv, scf, _
              iframe
              iframe #
              iapply BigSepM.bigSepM_empty.2
              itrivial
            (try wp_auto)
            iapply HΦ; itrivial
    · iunfold cliStreamErr at Hse0
      icases Hse0 with ⟨%Hce, #Hse, -⟩
      cases rerr with
      | nil => exact absurd rfl Hce.1
      | ok rei =>
        (try wp_auto)
        wp_apply wp_canceledByCaller sc scd _ $$ [] as %b -
        · iframe #
        cases b
        · (try wp_auto)
          wp_apply wp_ContextError sc scd (GoInterface.ok rei) $$ [] as %err' ⟨%Herr', #Hse'⟩
          · iframe #; ipureintro; exact fun _ => Hce.2
          (try wp_auto)
          ihave #Hrp : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.v3rpc.rpctypes $$ []
          · iPkgInit
          ihave ⟨%xnl, #Hnl⟩ := errNoLeader_of_init $$ Hrp
          (try wp_auto)
          wp_apply (wp_Is err' _ (Or.inl ⟨xnl, rfl⟩)) $$ [] as %bnl -
          · iframe #
          cases bnl
          · (try wp_auto)
            wp_for_post
            wp_apply +noauto time.wp_After as %tch %γt #Htch
            (try wp_auto)
            ihave #Hsc2 : iprop(context.isContextDef sc scd) $$ [Hscc]
            · iexact Hscc
            iunfold context.isContextDef at Hsc2
            icases Hsc2 with ⟨-, #HDoneS, -⟩
            wp_apply +noauto HDoneS as %chs %γs #Hdones
            wp_auto_lc 2
            wp_apply_core chan.wp_select_blocking
            iapply BigAndL.bigAndL_cons.2
            isplit
            · simp only [chan.blockingClausePre]
              iexists time.Time, inferInstance, inferInstance, inferInstance, inferInstance, tch, γt
              isplitr
              · ipureintro; rfl
              isplitr
              · iapply is_bag_is_chan $$ Htch
              iapply bag_recv_au $$ [$Hlc1 $Hlc2] Htch
              inext
              iintro %tm -
              (try wp_auto)
              wp_for_post
              iframe
            iapply BigAndL.bigAndL_cons.2
            isplit
            · simp only [chan.blockingClausePre]
              iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, chs, γs
              isplit
              · ipureintro; rfl
              isplit
              · iapply context.isContextDone_is_chan $$ Hdones
              iapply context.isContextDone_receive _ _ _ _ $$ Hdones
              iintro -
              (try wp_auto)
              ihave #HU := Hsce' $$ %Broadcast.Unknown
              wp_apply HU $$ [] as %e0 - %- -
              (try wp_auto)
              wp_for_post
              (try wp_auto)
              wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, Hinv⟩
              iunfold lessorInv at Hinv
              icases Hinv with ⟨%mref, %mm, %stv, %scf, %e, Hkas, Hm, HM, Hstf, Hscf, #Hscok, Herrf, Hreg⟩
              (try wp_auto)
              ihave #Htt : □ (True : IProp GF) $$ []
              · imodintro; itrivial
              wp_apply wp_broadcast_chan_close dc0 γd0 iprop(True) $$ [$Hpend $Htt] as -
              (try wp_auto)
              wp_func_lits
              wp_bind (App (App (Val (map.forRange _ _)) _) _)
              iapply wp_map_for_range (fun (keys : List w64) (i : Int) => iprop(∃ k0 : Loc,
                  "HM" ∷ ([∗map] k ↦ ka ∈ mm, ⌜k ∈ keys.take i.toNat⌝ ∨ kaOwn (GF := GF) γr ka) ∗
                  "ka" ∷ ka_ptr ↦ k0 ∗ "%Hi0" ∷ ⌜0 ≤ i⌝)) _ _ _ mref mm (DFrac.own 1) $$ Hm
              iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
              isplitl [HM ka]
              · iexists _
                simp only [named]
                iframe
                isplitl
                · iapply BigSepM.bigSepM_mono (fun _ => or_intro_r) $$ HM
                · ipureintro; omega
              isplitr
              · imodintro
                iintro %i %key %v ⟨%Hki, %Hmv⟩ HP
                iNamed HP
                (try wp_auto)
                icases (BigSepM.bigSepM_delete
                  (Φ := fun (k : w64) (ka : Loc) => iprop(⌜k ∈ keys.take i.toNat⌝ ∨ kaOwn (GF := GF) γr ka))
                  (m := mm) Hmv).1 $$ HM with ⟨Hka, HMr⟩
                icases Hka with (%Hin | Hka)
                · exfalso; exact not_mem_take_of_nodup Hknodup Hki Hin
                wp_apply wp_close γr v $$ [$Hka]
                (try wp_auto)
                unfold forMapPostcondition
                iright; ileft
                isplitr
                · ipureintro; rfl
                iexists _
                simp only [named]
                iframe
                isplitl
                · iapply (BigSepM.bigSepM_delete
                    (Φ := fun (k : w64) (ka : Loc) => iprop(⌜k ∈ keys.take (i + 1).toNat⌝ ∨ kaOwn (GF := GF) γr ka))
                    (m := mm) Hmv).2
                  isplitl []
                  · ileft; ipureintro
                    have := (mem_take_succ_iff Hki key).2 (Or.inr rfl)
                    rwa [show (i + 1).toNat = i.toNat + 1 by omega]
                  iapply BigSepM.bigSepM_mono (fun _ => or_mono (BI.pure_mono (fun h =>
                    List.take_subset_take_left _ (by omega) h)) .rfl) $$ HMr
                · ipureintro; omega
              · iintro HP Hm
                iNamed HP
                (try wp_auto)
                wp_apply wp_map_make1 (K := w64) (V := Loc) as %mref' Hm'
                (try wp_auto)
                wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hkas Hm' Hstf Hscf Herrf Hreg]
                · inext
                  unfold lessorInv
                  iexists mref', ∅, stv, scf, _
                  iframe
                  iframe #
                  iapply BigSepM.bigSepM_empty.2
                  itrivial
                (try wp_auto)
                iapply HΦ; itrivial
            iapply BigAndL.bigAndL_nil.2
            itrivial
          · (try wp_auto)
            wp_apply wp_closeRequireLeader l addr $$ []
            · iframe #
            (try wp_auto)
            wp_for_post
            wp_apply +noauto time.wp_After as %tch %γt #Htch
            (try wp_auto)
            ihave #Hsc2 : iprop(context.isContextDef sc scd) $$ [Hscc]
            · iexact Hscc
            iunfold context.isContextDef at Hsc2
            icases Hsc2 with ⟨-, #HDoneS, -⟩
            wp_apply +noauto HDoneS as %chs %γs #Hdones
            wp_auto_lc 2
            wp_apply_core chan.wp_select_blocking
            iapply BigAndL.bigAndL_cons.2
            isplit
            · simp only [chan.blockingClausePre]
              iexists time.Time, inferInstance, inferInstance, inferInstance, inferInstance, tch, γt
              isplitr
              · ipureintro; rfl
              isplitr
              · iapply is_bag_is_chan $$ Htch
              iapply bag_recv_au $$ [$Hlc1 $Hlc2] Htch
              inext
              iintro %tm -
              (try wp_auto)
              wp_for_post
              iframe
            iapply BigAndL.bigAndL_cons.2
            isplit
            · simp only [chan.blockingClausePre]
              iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, chs, γs
              isplit
              · ipureintro; rfl
              isplit
              · iapply context.isContextDone_is_chan $$ Hdones
              iapply context.isContextDone_receive _ _ _ _ $$ Hdones
              iintro -
              (try wp_auto)
              ihave #HU := Hsce' $$ %Broadcast.Unknown
              wp_apply HU $$ [] as %e0 - %- -
              (try wp_auto)
              wp_for_post
              (try wp_auto)
              wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, Hinv⟩
              iunfold lessorInv at Hinv
              icases Hinv with ⟨%mref, %mm, %stv, %scf, %e, Hkas, Hm, HM, Hstf, Hscf, #Hscok, Herrf, Hreg⟩
              (try wp_auto)
              ihave #Htt : □ (True : IProp GF) $$ []
              · imodintro; itrivial
              wp_apply wp_broadcast_chan_close dc0 γd0 iprop(True) $$ [$Hpend $Htt] as -
              (try wp_auto)
              wp_func_lits
              wp_bind (App (App (Val (map.forRange _ _)) _) _)
              iapply wp_map_for_range (fun (keys : List w64) (i : Int) => iprop(∃ k0 : Loc,
                  "HM" ∷ ([∗map] k ↦ ka ∈ mm, ⌜k ∈ keys.take i.toNat⌝ ∨ kaOwn (GF := GF) γr ka) ∗
                  "ka" ∷ ka_ptr ↦ k0 ∗ "%Hi0" ∷ ⌜0 ≤ i⌝)) _ _ _ mref mm (DFrac.own 1) $$ Hm
              iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
              isplitl [HM ka]
              · iexists _
                simp only [named]
                iframe
                isplitl
                · iapply BigSepM.bigSepM_mono (fun _ => or_intro_r) $$ HM
                · ipureintro; omega
              isplitr
              · imodintro
                iintro %i %key %v ⟨%Hki, %Hmv⟩ HP
                iNamed HP
                (try wp_auto)
                icases (BigSepM.bigSepM_delete
                  (Φ := fun (k : w64) (ka : Loc) => iprop(⌜k ∈ keys.take i.toNat⌝ ∨ kaOwn (GF := GF) γr ka))
                  (m := mm) Hmv).1 $$ HM with ⟨Hka, HMr⟩
                icases Hka with (%Hin | Hka)
                · exfalso; exact not_mem_take_of_nodup Hknodup Hki Hin
                wp_apply wp_close γr v $$ [$Hka]
                (try wp_auto)
                unfold forMapPostcondition
                iright; ileft
                isplitr
                · ipureintro; rfl
                iexists _
                simp only [named]
                iframe
                isplitl
                · iapply (BigSepM.bigSepM_delete
                    (Φ := fun (k : w64) (ka : Loc) => iprop(⌜k ∈ keys.take (i + 1).toNat⌝ ∨ kaOwn (GF := GF) γr ka))
                    (m := mm) Hmv).2
                  isplitl []
                  · ileft; ipureintro
                    have := (mem_take_succ_iff Hki key).2 (Or.inr rfl)
                    rwa [show (i + 1).toNat = i.toNat + 1 by omega]
                  iapply BigSepM.bigSepM_mono (fun _ => or_mono (BI.pure_mono (fun h =>
                    List.take_subset_take_left _ (by omega) h)) .rfl) $$ HMr
                · ipureintro; omega
              · iintro HP Hm
                iNamed HP
                (try wp_auto)
                wp_apply wp_map_make1 (K := w64) (V := Loc) as %mref' Hm'
                (try wp_auto)
                wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hkas Hm' Hstf Hscf Herrf Hreg]
                · inext
                  unfold lessorInv
                  iexists mref', ∅, stv, scf, _
                  iframe
                  iframe #
                  iapply BigSepM.bigSepM_empty.2
                  itrivial
                (try wp_auto)
                iapply HΦ; itrivial
            iapply BigAndL.bigAndL_nil.2
            itrivial
        · (try wp_auto)
          wp_for_post
          wp_for_post
          (try wp_auto)
          wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, Hinv⟩
          iunfold lessorInv at Hinv
          icases Hinv with ⟨%mref, %mm, %stv, %scf, %e, Hkas, Hm, HM, Hstf, Hscf, #Hscok, Herrf, Hreg⟩
          (try wp_auto)
          ihave #Htt : □ (True : IProp GF) $$ []
          · imodintro; itrivial
          wp_apply wp_broadcast_chan_close dc0 γd0 iprop(True) $$ [$Hpend $Htt] as -
          (try wp_auto)
          wp_func_lits
          wp_bind (App (App (Val (map.forRange _ _)) _) _)
          iapply wp_map_for_range (fun (keys : List w64) (i : Int) => iprop(∃ k0 : Loc,
              "HM" ∷ ([∗map] k ↦ ka ∈ mm, ⌜k ∈ keys.take i.toNat⌝ ∨ kaOwn (GF := GF) γr ka) ∗
              "ka" ∷ ka_ptr ↦ k0 ∗ "%Hi0" ∷ ⌜0 ≤ i⌝)) _ _ _ mref mm (DFrac.own 1) $$ Hm
          iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
          isplitl [HM ka]
          · iexists _
            simp only [named]
            iframe
            isplitl
            · iapply BigSepM.bigSepM_mono (fun _ => or_intro_r) $$ HM
            · ipureintro; omega
          isplitr
          · imodintro
            iintro %i %key %v ⟨%Hki, %Hmv⟩ HP
            iNamed HP
            (try wp_auto)
            icases (BigSepM.bigSepM_delete
              (Φ := fun (k : w64) (ka : Loc) => iprop(⌜k ∈ keys.take i.toNat⌝ ∨ kaOwn (GF := GF) γr ka))
              (m := mm) Hmv).1 $$ HM with ⟨Hka, HMr⟩
            icases Hka with (%Hin | Hka)
            · exfalso; exact not_mem_take_of_nodup Hknodup Hki Hin
            wp_apply wp_close γr v $$ [$Hka]
            (try wp_auto)
            unfold forMapPostcondition
            iright; ileft
            isplitr
            · ipureintro; rfl
            iexists _
            simp only [named]
            iframe
            isplitl
            · iapply (BigSepM.bigSepM_delete
                (Φ := fun (k : w64) (ka : Loc) => iprop(⌜k ∈ keys.take (i + 1).toNat⌝ ∨ kaOwn (GF := GF) γr ka))
                (m := mm) Hmv).2
              isplitl []
              · ileft; ipureintro
                have := (mem_take_succ_iff Hki key).2 (Or.inr rfl)
                rwa [show (i + 1).toNat = i.toNat + 1 by omega]
              iapply BigSepM.bigSepM_mono (fun _ => or_mono (BI.pure_mono (fun h =>
                List.take_subset_take_left _ (by omega) h)) .rfl) $$ HMr
            · ipureintro; omega
          · iintro HP Hm
            iNamed HP
            (try wp_auto)
            wp_apply wp_map_make1 (K := w64) (V := Loc) as %mref' Hm'
            (try wp_auto)
            wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hkas Hm' Hstf Hscf Herrf Hreg]
            · inext
              unfold lessorInv
              iexists mref', ∅, stv, scf, _
              iframe
              iframe #
              iapply BigSepM.bigSepM_empty.2
              itrivial
            (try wp_auto)
            iapply HΦ; itrivial
  · ihave #Herr' := Herr
    iunfold cliStreamErr at Herr'
    icases Herr' with ⟨%Hne, #Hse, -⟩
    subst Hst
    cases err with
    | nil => exact absurd rfl Hne.1
    | ok ei =>
      (try wp_auto)
      wp_apply wp_Error as %f1 -
      (try wp_auto)
      wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field) [f1]
      isplitr
      · ipureintro; rfl
      iintro %fsl ⟨-, -⟩
      (try wp_auto)
      wp_apply wp_Warn lg _ _ $$ []
      · iframe #; ipureintro; exact Hlgnn
      (try wp_auto)
      wp_apply wp_canceledByCaller sc scd _ $$ [] as %b -
      · iframe #
      cases b
      · (try wp_auto)
        wp_apply +noauto time.wp_After as %tch %γt #Htch
        (try wp_auto)
        ihave #Hsc2 : iprop(context.isContextDef sc scd) $$ [Hscc]
        · iexact Hscc
        iunfold context.isContextDef at Hsc2
        icases Hsc2 with ⟨-, #HDoneS, -⟩
        wp_apply +noauto HDoneS as %chs %γs #Hdones
        wp_auto_lc 2
        wp_apply_core chan.wp_select_blocking
        iapply BigAndL.bigAndL_cons.2
        isplit
        · simp only [chan.blockingClausePre]
          iexists time.Time, inferInstance, inferInstance, inferInstance, inferInstance, tch, γt
          isplitr
          · ipureintro; rfl
          isplitr
          · iapply is_bag_is_chan $$ Htch
          iapply bag_recv_au $$ [$Hlc1 $Hlc2] Htch
          inext
          iintro %tm -
          (try wp_auto)
          wp_for_post
          iframe
        iapply BigAndL.bigAndL_cons.2
        isplit
        · simp only [chan.blockingClausePre]
          iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, chs, γs
          isplit
          · ipureintro; rfl
          isplit
          · iapply context.isContextDone_is_chan $$ Hdones
          iapply context.isContextDone_receive _ _ _ _ $$ Hdones
          iintro -
          (try wp_auto)
          ihave #HU := Hsce' $$ %Broadcast.Unknown
          wp_apply HU $$ [] as %e0 - %- -
          (try wp_auto)
          wp_for_post
          (try wp_auto)
          wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, Hinv⟩
          iunfold lessorInv at Hinv
          icases Hinv with ⟨%mref, %mm, %stv, %scf, %e, Hkas, Hm, HM, Hstf, Hscf, #Hscok, Herrf, Hreg⟩
          (try wp_auto)
          ihave #Htt : □ (True : IProp GF) $$ []
          · imodintro; itrivial
          wp_apply wp_broadcast_chan_close dc0 γd0 iprop(True) $$ [$Hpend $Htt] as -
          (try wp_auto)
          wp_func_lits
          wp_bind (App (App (Val (map.forRange _ _)) _) _)
          iapply wp_map_for_range (fun (keys : List w64) (i : Int) => iprop(∃ k0 : Loc,
              "HM" ∷ ([∗map] k ↦ ka ∈ mm, ⌜k ∈ keys.take i.toNat⌝ ∨ kaOwn (GF := GF) γr ka) ∗
              "ka" ∷ ka_ptr ↦ k0 ∗ "%Hi0" ∷ ⌜0 ≤ i⌝)) _ _ _ mref mm (DFrac.own 1) $$ Hm
          iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
          isplitl [HM ka]
          · iexists _
            simp only [named]
            iframe
            isplitl
            · iapply BigSepM.bigSepM_mono (fun _ => or_intro_r) $$ HM
            · ipureintro; omega
          isplitr
          · imodintro
            iintro %i %key %v ⟨%Hki, %Hmv⟩ HP
            iNamed HP
            (try wp_auto)
            icases (BigSepM.bigSepM_delete
              (Φ := fun (k : w64) (ka : Loc) => iprop(⌜k ∈ keys.take i.toNat⌝ ∨ kaOwn (GF := GF) γr ka))
              (m := mm) Hmv).1 $$ HM with ⟨Hka, HMr⟩
            icases Hka with (%Hin | Hka)
            · exfalso; exact not_mem_take_of_nodup Hknodup Hki Hin
            wp_apply wp_close γr v $$ [$Hka]
            (try wp_auto)
            unfold forMapPostcondition
            iright; ileft
            isplitr
            · ipureintro; rfl
            iexists _
            simp only [named]
            iframe
            isplitl
            · iapply (BigSepM.bigSepM_delete
                (Φ := fun (k : w64) (ka : Loc) => iprop(⌜k ∈ keys.take (i + 1).toNat⌝ ∨ kaOwn (GF := GF) γr ka))
                (m := mm) Hmv).2
              isplitl []
              · ileft; ipureintro
                have := (mem_take_succ_iff Hki key).2 (Or.inr rfl)
                rwa [show (i + 1).toNat = i.toNat + 1 by omega]
              iapply BigSepM.bigSepM_mono (fun _ => or_mono (BI.pure_mono (fun h =>
                List.take_subset_take_left _ (by omega) h)) .rfl) $$ HMr
            · ipureintro; omega
          · iintro HP Hm
            iNamed HP
            (try wp_auto)
            wp_apply wp_map_make1 (K := w64) (V := Loc) as %mref' Hm'
            (try wp_auto)
            wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hkas Hm' Hstf Hscf Herrf Hreg]
            · inext
              unfold lessorInv
              iexists mref', ∅, stv, scf, _
              iframe
              iframe #
              iapply BigSepM.bigSepM_empty.2
              itrivial
            (try wp_auto)
            iapply HΦ; itrivial
        iapply BigAndL.bigAndL_nil.2
        itrivial
      · (try wp_auto)
        wp_for_post
        (try wp_auto)
        wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, Hinv⟩
        iunfold lessorInv at Hinv
        icases Hinv with ⟨%mref, %mm, %stv, %scf, %e, Hkas, Hm, HM, Hstf, Hscf, #Hscok, Herrf, Hreg⟩
        (try wp_auto)
        ihave #Htt : □ (True : IProp GF) $$ []
        · imodintro; itrivial
        wp_apply wp_broadcast_chan_close dc0 γd0 iprop(True) $$ [$Hpend $Htt] as -
        (try wp_auto)
        wp_func_lits
        wp_bind (App (App (Val (map.forRange _ _)) _) _)
        iapply wp_map_for_range (fun (keys : List w64) (i : Int) => iprop(∃ k0 : Loc,
            "HM" ∷ ([∗map] k ↦ ka ∈ mm, ⌜k ∈ keys.take i.toNat⌝ ∨ kaOwn (GF := GF) γr ka) ∗
            "ka" ∷ ka_ptr ↦ k0 ∗ "%Hi0" ∷ ⌜0 ≤ i⌝)) _ _ _ mref mm (DFrac.own 1) $$ Hm
        iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
        isplitl [HM ka]
        · iexists _
          simp only [named]
          iframe
          isplitl
          · iapply BigSepM.bigSepM_mono (fun _ => or_intro_r) $$ HM
          · ipureintro; omega
        isplitr
        · imodintro
          iintro %i %key %v ⟨%Hki, %Hmv⟩ HP
          iNamed HP
          (try wp_auto)
          icases (BigSepM.bigSepM_delete
            (Φ := fun (k : w64) (ka : Loc) => iprop(⌜k ∈ keys.take i.toNat⌝ ∨ kaOwn (GF := GF) γr ka))
            (m := mm) Hmv).1 $$ HM with ⟨Hka, HMr⟩
          icases Hka with (%Hin | Hka)
          · exfalso; exact not_mem_take_of_nodup Hknodup Hki Hin
          wp_apply wp_close γr v $$ [$Hka]
          (try wp_auto)
          unfold forMapPostcondition
          iright; ileft
          isplitr
          · ipureintro; rfl
          iexists _
          simp only [named]
          iframe
          isplitl
          · iapply (BigSepM.bigSepM_delete
              (Φ := fun (k : w64) (ka : Loc) => iprop(⌜k ∈ keys.take (i + 1).toNat⌝ ∨ kaOwn (GF := GF) γr ka))
              (m := mm) Hmv).2
            isplitl []
            · ileft; ipureintro
              have := (mem_take_succ_iff Hki key).2 (Or.inr rfl)
              rwa [show (i + 1).toNat = i.toNat + 1 by omega]
            iapply BigSepM.bigSepM_mono (fun _ => or_mono (BI.pure_mono (fun h =>
              List.take_subset_take_left _ (by omega) h)) .rfl) $$ HMr
          · ipureintro; omega
        · iintro HP Hm
          iNamed HP
          (try wp_auto)
          wp_apply wp_map_make1 (K := w64) (V := Loc) as %mref' Hm'
          (try wp_auto)
          wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hkas Hm' Hstf Hscf Herrf Hreg]
          · inext
            unfold lessorInv
            iexists mref', ∅, stv, scf, _
            iframe
            iframe #
            iapply BigSepM.bigSepM_empty.2
            itrivial
          (try wp_auto)
          iapply HΦ; itrivial

end proof

end EtcdGrove
end Perennial

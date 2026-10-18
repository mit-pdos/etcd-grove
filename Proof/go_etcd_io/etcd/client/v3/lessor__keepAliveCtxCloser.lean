/-
Proof of `Spec/go_etcd_io/etcd/client/v3/lessor__keepAliveCtxCloser.lean` (item 1, the client
lease). Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.lessor__keepAliveCtxCloser
public import Spec.context.ValueKeepAlive
public import Proof.Lib.Slice

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
theorem lessor.keepAliveCtxCloser.wp_proof
    (wp_Value : context.ValueKeepAlive.spec (GF := GF) (hG := hG)) :
    lessor.keepAliveCtxCloser.spec (GF := GF) (hG := hG) := by
  intro l addr ctx cd id kd γkd
  wp_start as ⟨#Hl, #Hctx, #Hkd⟩
  iunfold lessorAt at Hl
  icases Hl with ⟨%dc, %γd, %sc, %scd, %lg, %d, #Hdc, #Hdcu, #Hsc, #Hscc, #Hlg, %Hlgnn, #Hd,
    #Hrem, #Hmu, #Honce⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  ihave #Hctx2 : iprop(context.isContextDef ctx cd) $$ [Hctx]
  · iexact Hctx
  iunfold context.isContextDef at Hctx2
  icases Hctx2 with ⟨-, #HDoneC, -⟩
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply +noauto HDoneC as %ch1 %γ1 #Hdone1
  (try wp_auto)
  wp_apply_core chan.wp_select_blocking
  iapply BigAndL.bigAndL_cons.2
  isplit
  · simp only [chan.blockingClausePre]
    iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, kd, γkd
    isplit
    · ipureintro; rfl
    isplit
    · iapply ownBroadcastChan_is_chan $$ Hkd
    iapply broadcast_chan_receive _ _ _ _ _ $$ Hkd
    iintro -
    (try wp_auto)
    iapply HΦ; itrivial
  iapply BigAndL.bigAndL_cons.2
  isplit
  · simp only [chan.blockingClausePre]
    iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, dc, γd
    isplit
    · ipureintro; rfl
    isplit
    · iapply ownBroadcastChan_is_chan $$ Hdcu
    iapply broadcast_chan_receive _ _ _ _ _ $$ Hdcu
    iintro -
    (try wp_auto)
    iapply HΦ; itrivial
  iapply BigAndL.bigAndL_cons.2
  isplit
  · simp only [chan.blockingClausePre]
    iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, ch1, γ1
    isplit
    · ipureintro; rfl
    isplit
    · iapply context.isContextDone_is_chan $$ Hdone1
    iapply context.isContextDone_receive _ _ _ _ $$ Hdone1
    iintro -
    (try wp_auto)
    wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, Hinv⟩
    iunfold lessorInv at Hinv
    icases Hinv with ⟨%mref, %mm, %stv, %scf, %e, Hkas, Hm, HM, Hstf, Hscf, #Hscok, Herrf⟩
    (try wp_auto)
    wp_apply wp_map_lookup2 _ _ mref mm id (DFrac.own 1) $$ [$Hm] as Hm
    rcases Hlk : mm !! id with _ | ka
    · simp only [Option.getD_none, Option.isSome_none]
      (try wp_auto)
      wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hkas Hm HM Hstf Hscf Herrf]
      · inext; unfold lessorInv; iexists mref, mm, stv, scf, e; iframe; iframe #
      (try wp_auto)
      iapply HΦ; itrivial
    · simp only [Option.getD_some, Option.isSome_some, decide_true]
      icases (BigSepM.bigSepM_delete (Φ := fun (_ : w64) (ka : Loc) => kaOwn (GF := GF) ka)
        (m := mm) Hlk).1 $$ HM with ⟨Hka, HM⟩
      iunfold kaOwn at Hka
      icases Hka with ⟨%chsS, %ctxsS, %chs, %ctxs, %dl, %nk, %kd', %γkd', Hchs, Hchsl, Hchscap,
        Hctxs, Hctxsl, Hctxscap, %Hlen, Hdl, Hnk, #Hkd', Hpend, Htoks, #Hctxok⟩
      (try wp_auto)
      rename_i igo
      irename : (igo ↦ zero_val w64 : IProp GF) => gi
      ihave %Hcl := ownSlice_len $$ Hctxsl
      ihave %Hchl := ownSlice_len $$ Hchsl
      ihave IH : iprop(∃ (n iv : w64) (c0 : GoInterface),
          "i" ∷ i_ptr ↦ n ∗ "gi" ∷ igo ↦ iv ∗ "c" ∷ c_ptr ↦ c0 ∗
          "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.nat n ≤ ctxs.length⌝) $$ [i gi c]
      · iexists W64 0, _, _
        simp only [named]
        iframe
        ipureintro; constructor <;> word
      wp_for IH
      wp_if_destruct
      · have Hlt : sint.nat n < ctxs.length := by word
        have Hc : ctxs[sint.nat n]? = some (ctxs[sint.nat n]'Hlt) := List.getElem?_eq_getElem Hlt
        have Hbnd : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z ctxsS.len := ⟨Hn.1, by word⟩
        rw [ite_eq_left Hbnd]
        wp_apply wp_load_slice_index ctxsS (sint.Z n) _ (DFrac.own 1) (ctxs[sint.nat n]'Hlt) Hn.1
          $$ [Hctxsl] as Hctxsl
        · iframe; ipureintro; exact Hc
        (try wp_auto)
        ihave #Hco := BigSepL.bigSepL_lookup (Φ := fun _ c => kaCtxOk (GF := GF) c) Hc $$ Hctxok
        iunfold kaCtxOk at Hco
        icases Hco with ⟨%ci, %cdi, %Hcieq, #Hci⟩
        rw [Hcieq]
        (try wp_auto)
        wp_apply wp_Value ci _ cdi rfl $$ [$Hci] as %v1 %Hv1
        (try wp_auto)
        wp_apply wp_Value ctx _ cd rfl $$ [$Hctx] as %v2 %Hv2
        rcases Hv1 with rfl | ⟨p1, rfl⟩ <;> rcases Hv2 with rfl | ⟨p2, rfl⟩
        · (try wp_auto)
          have Hlt2 : sint.nat n < chs.length := by rw [Hlen]; exact Hlt
          have Hbnd2 : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z chsS.len := ⟨Hn.1, by word⟩
          rw [ite_eq_left Hbnd2]
          wp_apply wp_load_slice_index chsS (sint.Z n) _ (DFrac.own 1) (chs[sint.nat n]'Hlt2) Hn.1
            $$ [Hchsl] as Hchsl
          · iframe; ipureintro; exact List.getElem?_eq_getElem Hlt2
          icases bigSepL_eraseIdx (fun c => chanTok (GF := GF) c) chs (sint.nat n) Hlt2 $$ Htoks
            with ⟨Htok, Htoks⟩
          (try wp_auto)
          wp_apply wp_chanTok_close (chs[sint.nat n]'Hlt2) $$ [$Htok]
          (try wp_auto)
          ihave %Hcw := ownSlice_wf _ _ _ $$ Hctxsl
          ihave %Hchw := ownSlice_wf _ _ _ $$ Hchsl
          rw [ite_eq_left (by constructor <;> word)]
          (try wp_auto)
          rw [ite_eq_left (by constructor <;> word)]
          wp_apply (wp_slice_delete ctxsS ctxs n ⟨Hn.1, by word⟩) $$ [$Hctxsl $Hctxscap]
            as %ctxsS' ⟨Hctxsl, Hctxscap⟩
          (try wp_auto)
          rw [ite_eq_left (by constructor <;> word)]
          (try wp_auto)
          rw [ite_eq_left (by constructor <;> word)]
          wp_apply (wp_slice_delete chsS chs n ⟨Hn.1, by word⟩) $$ [$Hchsl $Hchscap]
            as %chsS' ⟨Hchsl, Hchscap⟩
          (try wp_auto)
          ihave #Hctxok' := bigSepL_eraseIdx (fun c => kaCtxOk (GF := GF) c) ctxs (sint.nat n) Hlt $$ Hctxok
          iclear Hctxok
          icases Hctxok' with ⟨-, #Hctxok⟩
          wp_for_post
          (try wp_auto)
          by_cases hz : chsS'.len = W64 0
          · rw [decide_eq_true hz]
            (try wp_auto)
            wp_apply wp_mapDelete $$ [$Hm] as Hm
            (try wp_auto)
            wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hkas Hm HM Hstf Hscf Herrf]
            · inext; unfold lessorInv; iexists mref, _, stv, scf, e; iframe; iframe #
            (try wp_auto)
            iapply HΦ; itrivial
          · rw [decide_eq_false hz]
            (try wp_auto)
            wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hkas Hm HM Hstf Hscf Herrf Hchs Hchsl Hchscap
              Hctxs Hctxsl Hctxscap Hdl Hnk Hpend Htoks]
            · inext
              unfold lessorInv
              iexists mref, mm, stv, scf, e
              iframe
              iframe #
              iapply (BigSepM.bigSepM_delete (Φ := fun (_ : w64) (ka : Loc) => kaOwn (GF := GF) ka)
                (m := mm) Hlk).2
              iframe HM
              unfold kaOwn
              iexists chsS', ctxsS', (chs.eraseIdx (sint.nat n)), (ctxs.eraseIdx (sint.nat n)), _, _, kd', γkd'
              iframe
              iframe #
              ipureintro; exact (by rw [List.length_eraseIdx_of_lt Hlt2, List.length_eraseIdx_of_lt Hlt, Hlen])
            (try wp_auto)
            iapply HΦ; itrivial
        · (try wp_auto)
          (try wp_auto)
          wp_for_post
          iframe
          iexists n + W64 1, _, _
          iframe
          ipureintro; constructor <;> word
        · (try wp_auto)
          (try wp_auto)
          wp_for_post
          iframe
          iexists n + W64 1, _, _
          iframe
          ipureintro; constructor <;> word
        · (try wp_auto)
          by_cases hp : p1 = p2
          · subst hp
            (try wp_auto)
            have Hlt2 : sint.nat n < chs.length := by rw [Hlen]; exact Hlt
            have Hbnd2 : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z chsS.len := ⟨Hn.1, by word⟩
            rw [ite_eq_left Hbnd2]
            wp_apply wp_load_slice_index chsS (sint.Z n) _ (DFrac.own 1) (chs[sint.nat n]'Hlt2) Hn.1
              $$ [Hchsl] as Hchsl
            · iframe; ipureintro; exact List.getElem?_eq_getElem Hlt2
            icases bigSepL_eraseIdx (fun c => chanTok (GF := GF) c) chs (sint.nat n) Hlt2 $$ Htoks
              with ⟨Htok, Htoks⟩
            (try wp_auto)
            wp_apply wp_chanTok_close (chs[sint.nat n]'Hlt2) $$ [$Htok]
            (try wp_auto)
            ihave %Hcw := ownSlice_wf _ _ _ $$ Hctxsl
            ihave %Hchw := ownSlice_wf _ _ _ $$ Hchsl
            rw [ite_eq_left (by constructor <;> word)]
            (try wp_auto)
            rw [ite_eq_left (by constructor <;> word)]
            wp_apply (wp_slice_delete ctxsS ctxs n ⟨Hn.1, by word⟩) $$ [$Hctxsl $Hctxscap]
              as %ctxsS' ⟨Hctxsl, Hctxscap⟩
            (try wp_auto)
            rw [ite_eq_left (by constructor <;> word)]
            (try wp_auto)
            rw [ite_eq_left (by constructor <;> word)]
            wp_apply (wp_slice_delete chsS chs n ⟨Hn.1, by word⟩) $$ [$Hchsl $Hchscap]
              as %chsS' ⟨Hchsl, Hchscap⟩
            (try wp_auto)
            ihave #Hctxok' := bigSepL_eraseIdx (fun c => kaCtxOk (GF := GF) c) ctxs (sint.nat n) Hlt $$ Hctxok
            iclear Hctxok
            icases Hctxok' with ⟨-, #Hctxok⟩
            wp_for_post
            (try wp_auto)
            by_cases hz : chsS'.len = W64 0
            · rw [decide_eq_true hz]
              (try wp_auto)
              wp_apply wp_mapDelete $$ [$Hm] as Hm
              (try wp_auto)
              wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hkas Hm HM Hstf Hscf Herrf]
              · inext; unfold lessorInv; iexists mref, _, stv, scf, e; iframe; iframe #
              (try wp_auto)
              iapply HΦ; itrivial
            · rw [decide_eq_false hz]
              (try wp_auto)
              wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hkas Hm HM Hstf Hscf Herrf Hchs Hchsl Hchscap
                Hctxs Hctxsl Hctxscap Hdl Hnk Hpend Htoks]
              · inext
                unfold lessorInv
                iexists mref, mm, stv, scf, e
                iframe
                iframe #
                iapply (BigSepM.bigSepM_delete (Φ := fun (_ : w64) (ka : Loc) => kaOwn (GF := GF) ka)
                  (m := mm) Hlk).2
                iframe HM
                unfold kaOwn
                iexists chsS', ctxsS', (chs.eraseIdx (sint.nat n)), (ctxs.eraseIdx (sint.nat n)), _, _, kd', γkd'
                iframe
                iframe #
                ipureintro; exact (by rw [List.length_eraseIdx_of_lt Hlt2, List.length_eraseIdx_of_lt Hlt, Hlen])
              (try wp_auto)
              iapply HΦ; itrivial
          · rw [decide_eq_false hp]
            (try wp_auto)
            (try wp_auto)
            wp_for_post
            iframe
            iexists n + W64 1, _, _
            iframe
            ipureintro; constructor <;> word
      · (try wp_auto)
        by_cases hz : chsS.len = W64 0
        · rw [decide_eq_true hz]
          (try wp_auto)
          wp_apply wp_mapDelete $$ [$Hm] as Hm
          (try wp_auto)
          wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hkas Hm HM Hstf Hscf Herrf]
          · inext; unfold lessorInv; iexists mref, _, stv, scf, e; iframe; iframe #
          (try wp_auto)
          iapply HΦ; itrivial
        · rw [decide_eq_false hz]
          (try wp_auto)
          wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hkas Hm HM Hstf Hscf Herrf Hchs Hchsl Hchscap
            Hctxs Hctxsl Hctxscap Hdl Hnk Hpend Htoks]
          · inext
            unfold lessorInv
            iexists mref, mm, stv, scf, e
            iframe
            iframe #
            iapply (BigSepM.bigSepM_delete (Φ := fun (_ : w64) (ka : Loc) => kaOwn (GF := GF) ka)
              (m := mm) Hlk).2
            iframe HM
            unfold kaOwn
            iexists chsS, ctxsS, chs, ctxs, _, _, kd', γkd'
            iframe
            iframe #
            ipureintro; exact Hlen
          (try wp_auto)
          iapply HΦ; itrivial
  iapply BigAndL.bigAndL_nil.2
  itrivial

end proof

end EtcdGrove
end Perennial

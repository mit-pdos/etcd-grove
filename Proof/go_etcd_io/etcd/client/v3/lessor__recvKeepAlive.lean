/-
Proof of `Spec/go_etcd_io/etcd/client/v3/lessor__recvKeepAlive.lean` (item 1, the client lease).
Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.lessor__recvKeepAlive
public import Spec.go_etcd_io.etcd.client.v3.keepAlive__close
public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb.LeaseKeepAliveResponse__GetHeader
public import Spec.go_uber_org.zap.Int
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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

set_option maxHeartbeats 0 in
theorem lessor.recvKeepAlive.wp_proof
    (wp_GetHeader : LeaseKeepAliveResponse.GetHeader.spec (GF := GF) (hG := hG))
    (wp_close : keepAlive.close.spec (GF := GF) (hG := hG))
    (wp_Int : zap.Int'.spec (GF := GF) (hG := hG))
    (wp_Warn : zap.Logger.Warn.spec (GF := GF) (hG := hG)) :
    lessor.recvKeepAlive.spec (GF := GF) (hG := hG) := by
  intro l addr resp m
  wp_start as ⟨#Hl, #Hresp⟩
  iunfold keepAliveRespMsg at Hresp
  icases Hresp with ⟨%Hnn, %h, #Hh, #Hid, #Httl⟩
  iunfold lessorAt at Hl
  icases Hl with ⟨%dc, %γd, %sc, %scd, %lg, %d, %γr, #Hdc, #Hdcu, #Hsc, #Hscc, #Hlg, %Hlgnn, #Hd,
    #Hrem, #Hmu, #Honce⟩
  ihave #Hpb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb $$ []
  · iPkgInit
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply wp_GetHeader resp h DFrac.discard $$ [] as -
  · iframe #; ipureintro; exact Hnn
  (try wp_auto)
  wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, Hinv⟩
  iunfold lessorInv at Hinv
  icases Hinv with ⟨%mref, %mm, %st, %scf, %e, Hkas, Hm, HM, Hst, Hscf, #Hscok, Herr, Hreg⟩
  (try wp_auto)
  simp only
  wp_apply wp_map_lookup2 _ _ mref mm m.1 (DFrac.own 1) $$ [Hm] as Hm
  · iexact Hm
  rcases Hlk : mm !! m.1 with _ | ka
  · simp only [Option.getD_none, Option.isSome_none, decide_false]
    (try wp_auto)
    wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hkas Hm HM Hst Hscf Herr Hreg]
    · inext; unfold lessorInv; iexists mref, mm, st, scf, e; iframe; iframe #
    (try wp_auto)
    iapply HΦ; itrivial
  · simp only [Option.getD_some, Option.isSome_some, decide_true]
    (try wp_auto)
    wp_if_destruct
    · (try wp_auto)
      wp_apply wp_mapDelete mref mm m.1 _ _ $$ [$Hm] as Hm
      icases (BigSepM.bigSepM_delete (Φ := fun (_ : w64) (ka : Loc) => kaOwn (GF := GF) γr ka) (m := mm) Hlk).1 $$ HM
        with ⟨Hka, HM⟩
      (try wp_auto)
      wp_apply wp_close γr ka $$ [$Hka]
      (try wp_auto)
      wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hkas Hm HM Hst Hscf Herr Hreg]
      · inext; unfold lessorInv; iexists mref, _, st, scf, e; iframe; iframe #
      (try wp_auto)
      iapply HΦ; itrivial
    · icases (BigSepM.bigSepM_lookup_acc (Φ := fun (_ : w64) (ka : Loc) => kaOwn (GF := GF) γr ka) (m := mm) Hlk).1 $$ HM
        with ⟨Hka, HMback⟩
      iunfold kaOwn at Hka
      icases Hka with ⟨%chsS, %ctxsS, %chs, %ctxs, %dl, %nk, %kd, %γkd, Hchs, Hchsl, Hchscap,
        Hctxs, Hctxsl, Hctxscap, %Hlen, Hdl, Hnk, #Hkd, Hpend, Htoks, #Hctxok, #Hpair⟩
      (try wp_auto)
      wp_apply time.wp_Now as %t1 -
      wp_apply time.Time.wp_Add as %t2 -
      (try wp_auto)
      wp_apply time.wp_Now as %t3 -
      wp_apply time.Time.wp_Add as %t4 -
      (try wp_auto)
      ihave %Hsll := ownSlice_len $$ Hchsl
      ihave IH : iprop(∃ (n : w64) (c0 : GoChan) (nk' : time.Time),
          "i" ∷ i_ptr ↦ n ∗ "ch" ∷ ch_ptr ↦ c0 ∗ "Hchsl" ∷ chsS ↦* chs ∗
          "Htoks" ∷ ([∗list] c ∈ chs, chanTok c) ∗ "Hnk" ∷ kaF go!"nextKeepAlive" ka ↦ nk' ∗
          "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.nat n ≤ chs.length⌝) $$ [i ch Hchsl Htoks Hnk]
      · iexists W64 0, _, _
        simp only [named]
        iframe
        ipureintro; constructor <;> word
      wp_for IH
      wp_if_destruct
      · have Hlt : sint.nat n < chs.length := by word
        have Hc : chs[sint.nat n]? = some (chs[sint.nat n]'Hlt) := List.getElem?_eq_getElem Hlt
        have Hbnd : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z chsS.len := ⟨Hn.1, by word⟩
        rw [ite_eq_left Hbnd]
        wp_apply wp_load_slice_index chsS (sint.Z n) _ (DFrac.own 1) (chs[sint.nat n]'Hlt) Hn.1
          $$ [Hchsl] as Hchsl
        · iframe; ipureintro; exact Hc
        (try wp_auto)
        icases bigSepL_get_acc (fun c => chanTok (GF := GF) c) chs (sint.nat n) Hlt $$ Htoks with ⟨Htok, Htoksback⟩
        iunfold chanTok at Htok
        icases Htok with ⟨%γ, %γc, #Hch, #Hinv, Hgv⟩
        wp_bind (App (Val (GoInstruction SelectStmt)) _)
        iapply chan.wp_select_nonblocking
        isplit
        · iapply BigAndL.bigAndL_cons.2
          isplit
          · simp only [chan.nonblockingClausePre]
            iexists Loc, inferInstance, inferInstance, inferInstance, inferInstance,
              (chs[sint.nat n]'Hlt), γ, «$r0_ptr»
            isplit
            · ipureintro; exact ⟨rfl, rfl⟩
            isplit
            · iexact Hch
            unfold nonblockingSendAu
            isplit
            · iapply chanTok_nonblockingSend γ γc «$r0_ptr» $$ Hinv Hgv
              inext
              iintro Hgv
              (try wp_auto)
              wp_for_post
              iframe
              iexists n + W64 1, _, _
              iframe
              isplitl [Htoksback Hgv]
              · iapply Htoksback
                unfold chanTok
                iexists γ, γc
                iframe #
                iframe
              ipureintro; constructor <;> word
            · itrivial
          · iapply BigAndL.bigAndL_nil.2; itrivial
        · (try wp_auto)
          rw [decide_eq_false Hlgnn]
          (try wp_auto)
          ihave #Hzap : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
          · iPkgInit
          wp_apply wp_kaChan_len _ γ $$ [$Hch] as %n1 -
          wp_apply wp_Int as %f1 -
          (try wp_auto)
          wp_apply chan.wp_cap (V := Loc) _ γ $$ [$Hch]
          wp_apply wp_Int as %f2 -
          (try wp_auto)
          wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field) [f1, f2]
          isplitr
          · ipureintro; rfl
          iintro %fsl ⟨-, -⟩
          (try wp_auto)
          wp_apply wp_Warn lg _ _ $$ []
          · iframe #; ipureintro; exact Hlgnn
          (try wp_auto)
          wp_for_post
          iframe
          iexists n + W64 1, _, _
          iframe
          isplitl [Htoksback Hgv]
          · iapply Htoksback
            unfold chanTok
            iexists γ, γc
            iframe #
            iframe
          ipureintro; constructor <;> word
      · (try wp_auto)
        wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hkas Hm HMback Hst Hscf Herr Hreg Hchs Hchsl
          Hchscap Hctxs Hctxsl Hctxscap Hdl Hnk Hpend Htoks]
        · inext
          unfold lessorInv
          iexists mref, mm, st, scf, e
          iframe
          iframe #
          iapply HMback
          unfold kaOwn
          iexists chsS, ctxsS, chs, ctxs, _, _, kd, γkd
          iframe
          iframe #
          ipureintro; exact Hlen
        (try wp_auto)
        iapply HΦ; itrivial

end proof

end EtcdGrove
end Perennial

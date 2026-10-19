/-
Proof of `Spec/go_etcd_io/etcd/client/v3/lessor__deadlineLoop.lean` (item 1, the client lease).
Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.lessor__deadlineLoop
public import Spec.go_etcd_io.etcd.client.v3.keepAlive__close

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
theorem lessor.deadlineLoop.wp_proof (wp_close : keepAlive.close.spec (GF := GF) (hG := hG)) :
    lessor.deadlineLoop.spec (GF := GF) (hG := hG) := by
  intro l addr
  wp_start as #Hl
  iunfold lessorAt at Hl
  icases Hl with ⟨%dc, %γd, %sc, %scd, %lg, %d, %γr, #Hdc, #Hdcu, #Hsc, #Hscc, #Hlg, %Hlgnn, #Hd,
    #Hrem, #Hmu, #Honce⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply time.wp_NewTimer as %t %tch %γt #Ht
  (try wp_auto)
  iunfold time.isTimer at Ht
  icases Ht with ⟨#HtC, #Htbag, #Htm⟩
  ipersist l
  ipersist timer
  wp_for
  wp_apply +noauto time.Timer.wp_Reset t tch γt _ $$ [] as %b -
  · iunfold time.isTimer; iframe #
  wp_auto_lc 2
  wp_apply_core chan.wp_select_blocking
  iapply BigAndL.bigAndL_cons.2
  isplit
  · simp only [chan.blockingClausePre]
    iexists time.Time, inferInstance, inferInstance, inferInstance, inferInstance, tch, γt
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply is_bag_is_chan $$ Htbag
    iapply bag_recv_au $$ [$Hlc1 $Hlc2] Htbag
    inext
    iintro %tm -
    (try wp_auto)
    wp_apply time.wp_Now as %now -
    (try wp_auto)
    wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, Hinv⟩
    iunfold lessorInv at Hinv
    icases Hinv with ⟨%mref, %mm, %st, %scf, %e, Hkas, Hm, HM, Hst, Hscf, #Hscok, Herr, Hreg⟩
    (try wp_auto)
    wp_func_lits
    wp_bind (App (App (Val (map.forRange _ _)) _) _)
    iapply wp_map_for_range_mut (fun (i : Nat) (m' : GMap w64 Loc) =>
        iprop(∃ (k0 : Loc) (i0 : w64),
        "HM" ∷ ([∗map] _id ↦ ka ∈ m', kaOwn (GF := GF) γr ka) ∗
        "Hkas" ∷ lsF go!"keepAlives" l ↦ mref ∗
        "ka" ∷ ka_ptr ↦ k0 ∗ "id" ∷ id_ptr ↦ i0 ∗ "now" ∷ now_ptr ↦ now))
      _ _ _ mref mm $$ Hm
    iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
    isplitl [HM Hkas ka id now]
    · iexists _, _
      simp only [named]
      iframe
    isplitr
    · imodintro
      iintro %i %key %v %m' ⟨%Hki, %Hmv, %Hagree⟩ HP Hm
      iNamed HP
      have Hm'v : m' !! key = some v := by rw [Hagree i key (Nat.le_refl _) Hki]; exact Hmv
      (try wp_auto)
      icases (BigSepM.bigSepM_delete (Φ := fun (_ : w64) (ka : Loc) => kaOwn (GF := GF) γr ka)
        (m := m') Hm'v).1 $$ HM with ⟨Hka, HM⟩
      iunfold kaOwn at Hka
      icases Hka with ⟨%chsS, %ctxsS, %chs, %ctxs, %dl, %nk, %kd, %γkd, Hchs, Hchsl, Hchscap,
        Hctxs, Hctxsl, Hctxscap, %Hlen, Hdl, Hnk, #Hkd, Hpend, Htoks, #Hctxok, #Hpair⟩
      wp_apply time.Time.wp_ptr_Before $$ [$Hdl] as %bb Hdl
      wp_if_destruct
      · unfold forMapPostcondition
        iright; ileft
        isplitr
        · ipureintro; rfl
        iexists m'
        iframe Hm
        isplitl
        · iexists _, _
          simp only [named]
          iframe
          iapply (BigSepM.bigSepM_delete (Φ := fun (_ : w64) (ka : Loc) => kaOwn (GF := GF) γr ka)
            (m := m') Hm'v).2
          iframe HM
          unfold kaOwn
          iexists chsS, ctxsS, chs, ctxs, _, _, kd, γkd
          iframe
          iframe #
          ipureintro; exact Hlen
        ipureintro; intro k _; rfl
      · (try wp_auto)
        wp_apply wp_close γr v $$ [Hchs Hchsl Hchscap Hctxs Hctxsl Hctxscap Hdl Hnk Hpend Htoks]
        · unfold kaOwn
          iexists chsS, ctxsS, chs, ctxs, _, _, kd, γkd
          iframe
          iframe #
          ipureintro; exact Hlen
        (try wp_auto)
        wp_apply wp_mapDelete $$ [$Hm] as Hm
        unfold forMapPostcondition
        iright; ileft
        isplitr
        · ipureintro; rfl
        iexists _
        iframe Hm
        isplitl
        · iexists _, _
          simp only [named]
          iframe
        ipureintro
        intro k hk
        rw [GMap.lookup_delete_ne _ (Ne.symm hk)]
    iintro %m' HP Hm
    iNamed HP
    (try wp_auto)
    wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hkas Hm HM Hst Hscf Herr Hreg]
    · inext; unfold lessorInv; iexists mref, m', st, scf, e; iframe; iframe #
    (try wp_auto)
    wp_for_post
    iframe
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
    wp_for_post
    (try wp_auto)
    wp_apply time.Timer.wp_Stop t $$ [] as %b2 -
    · ileft; iexists tch, γt; iunfold time.isTimer; iframe #
    (try wp_auto)
    iapply HΦ
    itrivial
  iapply BigAndL.bigAndL_nil.2
  itrivial

end proof

end EtcdGrove
end Perennial

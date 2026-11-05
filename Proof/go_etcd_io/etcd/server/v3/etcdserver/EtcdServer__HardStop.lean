/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__HardStop.lean`. Lean-first (no Rocq
counterpart; the restart plan's R2b-2, 2026-11-02).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__HardStop

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- Taking the escrowed image out of `done`'s invariant with the claim. -/
theorem srvDoneInv_take (γ : SrvRaft) (ρ : ReqNames) (id : w64) (dd : GoString) (c : GName) :
    srvDoneInv (GF := GF) γ ρ id dd c -∗ token c ={⊤}=∗ ▷ srvDiskImage γ ρ id dd := by
  iintro #Hi Hc
  iunfold srvDoneInv at Hi
  iinv Hi with Hx Hclose
  icases Hx with (Himg | Hc')
  · imod Hclose $$ [Hc]
    · inext; iright; iexact Hc
    imodintro; iexact Himg
  · imod Hc'
    iexfalso
    iapply token_exclusive c $$ Hc Hc'

theorem EtcdServer.HardStop.wp_proof : EtcdServer.HardStop.spec (GF := GF) (hG := hG) := by
  intro s E γ ρ id dd
  wp_start as ⟨Hr, #Hba⟩
  iunfold srvStopRight at Hr
  icases Hr with ⟨%stc, %dnc, %γst, %γd, %c, #Hstc, #Hbag, #Hdnc, #Hdn, Hc, -⟩
  ihave #Hdch := ownBroadcastChan_is_chan _ _ _ _ $$ Hdn
  wp_auto_lc 4
  wp_apply_core chan.wp_select_blocking_nil
  -- `s.stop <- struct{}{}`
  iapply BigAndL.bigAndL_cons.2
  isplit
  · ileft
    simp only [chan.blockingClausePre]
    iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, stc, γst, ()
    isplitr
    · ipureintro; exact ⟨rfl, rfl⟩
    isplitr
    · iapply is_bag_is_chan $$ Hbag
    iapply bag_send_au γst stc _ () _ $$ [$Hlc1 $Hlc2] Hbag []
    · iexact Hba
    inext
    wp_auto
    wp_apply_core chan.wp_receive dnc γd $$ Hdch
    iintro ⟨Hlc5, Hlc6, Hlc7, _⟩
    iapply broadcast_chan_receive dnc γd _ _ .Unknown $$ Hdn
    iintro ⟨#Hinv, _⟩
    imod srvDoneInv_take γ ρ id dd c $$ Hinv Hc with Himg
    imod (lc_fupd_elim_later (E := ⊤)) $$ Hlc5 Himg with Himg
    wp_auto
    iapply HΦ
    iexact Himg
  -- `<-s.done`: closed
  iapply BigAndL.bigAndL_cons.2
  isplit
  · ileft
    simp only [chan.blockingClausePre]
    iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, dnc, γd
    isplitr
    · ipureintro; rfl
    isplitr
    · iexact Hdch
    iapply broadcast_chan_receive dnc γd _ _ .Unknown $$ Hdn
    iintro ⟨#Hinv, _⟩
    imod srvDoneInv_take γ ρ id dd c $$ Hinv Hc with Himg
    imod (lc_fupd_elim_later (E := ⊤)) $$ Hlc3 Himg with Himg
    wp_auto
    iapply HΦ
    iexact Himg
  iapply BigAndL.bigAndL_nil.2
  itrivial

end proof

end EtcdGrove
end Perennial

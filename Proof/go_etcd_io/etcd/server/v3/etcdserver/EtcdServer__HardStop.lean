/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__HardStop.lean`. Lean-first (no Rocq
counterpart; the restart plan's R2b-2, 2026-11-02).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__HardStop
import all Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRestart

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

/-- Taking the escrow out of `done`'s invariant with the claim. -/
theorem srvDoneInvG_take (Img : IProp GF) (c : GName) :
    srvDoneInvG (GF := GF) Img c -∗ token c ={⊤}=∗ ▷ Img := by
  iintro #Hi Hc
  iunfold srvDoneInvG at Hi
  iinv Hi with Hx Hclose
  icases Hx with (Himg | Hc')
  · imod Hclose $$ [Hc]
    · inext; iright; iexact Hc
    imodintro; iexact Himg
  · imod Hc'
    iexfalso
    iapply token_exclusive c $$ Hc Hc'

/-- `HardStop` at any escrow (`InvRestart.lean`'s `HardStop.specG`; etcd_safe P5). -/
theorem EtcdServer.HardStop.wp_proofG : EtcdServer.HardStop.specG (GF := GF) (hG := hG) := by
  intro s E ρ dd Img
  wp_start as ⟨Hr, Hba⟩
  iunfold srvStopRightG at Hr
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
    iapply bag_send_au γst stc _ () _ $$ [$Hlc1 $Hlc2] Hbag [Hba]
    · iexact Hba
    inext
    wp_auto
    wp_apply_core chan.wp_receive dnc γd $$ Hdch
    iintro ⟨Hlc5, Hlc6, Hlc7, _⟩
    iapply broadcast_chan_receive dnc γd _ _ .Unknown $$ Hdn
    iintro ⟨#Hinv, _⟩
    imod srvDoneInvG_take Img c $$ Hinv Hc with Himg
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
    imod srvDoneInvG_take Img c $$ Hinv Hc with Himg
    imod (lc_fupd_elim_later (E := ⊤)) $$ Hlc3 Himg with Himg
    wp_auto
    iapply HΦ
    iexact Himg
  iapply BigAndL.bigAndL_nil.2
  itrivial

theorem EtcdServer.HardStop.wp_proof : EtcdServer.HardStop.spec (GF := GF) (hG := hG) := by
  intro s E γ ρ id dd
  rw [srvStopRight_eq_G]
  exact EtcdServer.HardStop.wp_proofG s E ρ dd (srvDiskImage γ ρ id dd)

end proof

end EtcdGrove
end Perennial

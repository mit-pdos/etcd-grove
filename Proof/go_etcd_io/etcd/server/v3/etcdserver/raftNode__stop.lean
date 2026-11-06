/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/raftNode__stop.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.raftNode__stop

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

/-- (2026-11-03, R2b-3b) `raftNode.stop.spec`: the loop stopped, then the image out of `done`'s
escrow (`rn_esc_take`). (R2c review F2, 2026-11-06: until then `wp_proofStop`, beside a
`wp_proof` of a weaker `spec` without the image, used only by the `run.spec` R2c-4 removed.) -/
theorem raftNode.stop.wp_proof : raftNode.stop.spec (GF := GF) (hG := hG) := by
  intro E γ r A
  wp_start as ⟨#Hr, HST, Hrun, Hwt, Hsc, Happ⟩
  iunfold isRaftNode at Hr
  iNamed Hr
  iunfold rnWalTokA at Hwt
  icases Hwt with ⟨%st', #Hst', Hwo, Hwap, -⟩
  icombine Hst Hst' gives %Hsteq
  have Hsteq' : st' = st := by first | exact Hsteq.symm | exact Hsteq.2.symm
  subst Hsteq'
  iunfold rnStopBag at Hstci
  icases Hstci with ⟨%γs, #Hbag⟩
  ihave #Hdch := ownBroadcastChan_is_chan _ _ _ _ $$ Hdnci
  wp_auto_lc 4
  wp_apply_core chan.wp_select_blocking_nil
  -- `r.stopped <- struct{}{}`
  iapply BigAndL.bigAndL_cons.2
  isplit
  · ileft
    simp only [chan.blockingClausePre]
    iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, stc, γs, ()
    isplitr
    · ipureintro; exact ⟨rfl, rfl⟩
    isplitr
    · iapply is_bag_is_chan $$ Hbag
    iapply bag_send_au γs stc _ () _ $$ [$Hlc1 $Hlc2] Hbag [HST Hrun Hwo Hwap]
    · iframe HST Hrun Hwo Hwap
    inext
    wp_auto
    wp_apply_core chan.wp_receive dnc γ.done $$ Hdch
    iintro ⟨Hlc5, Hlc6, Hlc7, _⟩
    iapply broadcast_chan_receive dnc γ.done _ _ .Unknown $$ Hdnci
    iintro ⟨#Hesc, _⟩
    imod rn_esc_take E γ apc (storage.walOf st') A $$ Hapci Hesc Hsc Happ Hlc5 Hlc6
      with ⟨Hvac, %S, %σ, HrS, Hcl, %Hord⟩
    wp_auto
    iapply HΦ
    iframe Hvac
    iexists S, σ
    iframe HrS
    isplitl [Hcl]
    · iunfold rnWalClosed; iexists st'; iframe Hst Hcl
    ipureintro; exact Hord
  -- `<-r.done`: closed
  iapply BigAndL.bigAndL_cons.2
  isplit
  · ileft
    simp only [chan.blockingClausePre]
    iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, dnc, γ.done
    isplitr
    · ipureintro; rfl
    isplitr
    · iexact Hdch
    iapply broadcast_chan_receive dnc γ.done _ _ .Unknown $$ Hdnci
    iintro ⟨#Hesc, _⟩
    imod rn_esc_take E γ apc (storage.walOf st') A $$ Hapci Hesc Hsc Happ Hlc3 Hlc4
      with ⟨Hvac, %S, %σ, HrS, Hcl, %Hord⟩
    wp_auto
    iapply HΦ
    iframe Hvac
    iexists S, σ
    iframe HrS
    isplitl [Hcl]
    · iunfold rnWalClosed; iexists st'; iframe Hst Hcl
    ipureintro; exact Hord
  iapply BigAndL.bigAndL_nil.2
  itrivial

end proof

end EtcdGrove
end Perennial

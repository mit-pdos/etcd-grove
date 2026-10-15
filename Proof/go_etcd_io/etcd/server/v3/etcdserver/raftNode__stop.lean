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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

theorem raftNode.stop.wp_proof : raftNode.stop.spec (GF := GF) (hG := hG) := by
  intro E γ r
  wp_start as #Hr
  iunfold isRaftNode at Hr
  iNamed Hr
  iunfold isUnitBag at Hstci
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
    iapply bag_send_au γs stc (fun _ => iprop(True)) () _ $$ [$Hlc1 $Hlc2] Hbag []
    · itrivial
    inext
    wp_auto
    wp_apply_core chan.wp_receive dnc γ.done $$ Hdch
    iintro ⟨Hlc5, Hlc6, Hlc7, _⟩
    iapply broadcast_chan_receive dnc γ.done iprop(True) _ .Unknown $$ Hdnci
    iintro ⟨_, _⟩
    wp_auto
    iapply HΦ
    itrivial
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
    iapply broadcast_chan_receive dnc γ.done iprop(True) _ .Unknown $$ Hdnci
    iintro ⟨_, _⟩
    wp_auto
    iapply HΦ
    itrivial
  iapply BigAndL.bigAndL_nil.2
  itrivial

end proof

end EtcdGrove
end Perennial

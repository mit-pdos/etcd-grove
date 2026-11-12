/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/rafthttp/streamReader__stop.lean`. Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.streamReader__stop
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.streamReader__close

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.api go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Assumptions]

theorem rafthttp.streamReader.stop.wp_proof
    (hClose : rafthttp.streamReader.close.spec (GF := GF) (hG := hG)) :
    rafthttp.streamReader.stop.spec (GF := GF) (hG := hG) := by
  intro Rh lid pid γd cr
  wp_start as ⟨#Hf, #Hstop⟩
  ihave #Hf' := Hf
  iunfold srFixed at Hf'
  icases Hf' with ⟨%lg, %tr, %ps, %rc, %pc, %γr, %γp, %ctx, %cd, -, -, -, -, -, -, -, -, -, -, -,
    #Hmu, -, -⟩
  iunfold srStopRight at Hstop
  icases Hstop with ⟨%cf, %γc, %dc, %γdn, #Hcf, #Hcancel, #Hdc, #Hdone⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply sync.Mutex.wp_Lock _ (srLockInv cr) $$ [$Hmu] as ⟨Hlocked, Hinv⟩
  (try wp_auto)
  iunfold context.cancelSpec at Hcancel
  wp_apply Hcancel
  · imodintro; itrivial
  iintro -
  (try wp_auto)
  iunfold srLockInv at Hinv
  icases Hinv with ⟨%p, %c, Hp, Hc, Hcor⟩
  wp_apply hClose Rh lid pid γd cr c $$ [$Hf $Hc $Hcor] as Hc
  (try wp_auto)
  wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hp Hc]
  · inext
    iunfold srLockInv
    iexists _, _
    iframe
    ileft; ipureintro; rfl
  (try wp_auto)
  ihave #Hdcc := ownBroadcastChan_is_chan _ _ _ _ $$ Hdone
  wp_bind (App (Val (chan.receive _)) (Val #dc))
  wp_apply_core chan.wp_receive (V := Unit) dc γdn $$ Hdcc
  iintro -
  iapply broadcast_chan_receive dc γdn iprop(True) _ .Unknown $$ Hdone
  iintro ⟨-, -⟩
  (try wp_auto)
  iapply HΦ
  itrivial

end proof

end EtcdGrove
end Perennial

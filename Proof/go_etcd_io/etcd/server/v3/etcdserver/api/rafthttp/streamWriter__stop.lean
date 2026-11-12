/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/rafthttp/streamWriter__stop.lean`.
Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.streamWriter__stop

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

theorem rafthttp.streamWriter.stop.wp_proof :
    rafthttp.streamWriter.stop.spec (GF := GF) (hG := hG) := by
  intro Rh ty lid pid Rr cw
  wp_start as ⟨#Hf, Hstop⟩
  iunfold swFixed at Hf
  icases Hf with ⟨%lg, %ps, %fs, %r, %γd, %cc, %sc, %dc, %γc, %γs, %γdn, -, -, -, -, -, -, -, -,
    -, -, -, -, -, -, -, #Hdc, #Hdone⟩
  iunfold swStopRight at Hstop
  icases Hstop with ⟨%sc', %γs', #Hsc', Hbc⟩
  wp_auto
  wp_apply (wp_broadcast_chan_close sc' γs' iprop(True)) $$ [$Hbc] as -
  · imodintro; itrivial
  (try wp_auto)
  ihave #Hdcc := ownBroadcastChan_is_chan _ _ _ _ $$ Hdone
  wp_bind (App (Val (chan.receive _)) (Val #dc))
  wp_apply_core chan.wp_receive (V := Unit) dc γdn $$ Hdcc
  iintro -
  iapply broadcast_chan_receive dc γdn iprop(True) _ .Unknown $$ Hdone
  iintro ⟨-, -⟩
  wp_auto
  iapply HΦ
  itrivial

end proof

end EtcdGrove
end Perennial

/-
Proof of the spec of the same name (the watch slice's unit W-S). Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.serverWatchStream__close
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.watchStream__Close

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.api
  go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

theorem v3rpc.serverWatchStream.close.wp_proof
    (hClose : mvcc.watchStream.Close.spec (GF := GF) (hG := hG)) :
    v3rpc.serverWatchStream.close.spec (GF := GF) (hG := hG) := by
  intro sws r n P
  wp_start as ⟨#Hsws, Hopen, Hcc, Hadd⟩
  ihave #Hsws' := Hsws
  iunfold v3rpc.swsIs at Hsws'
  icases Hsws' with ⟨%Hnn, -, -, -, -, -, -, -, -, #Fws, -, -, -, -, #Fcc, -, -, -, -, -, #Hwstream,
    -⟩
  ihave #Pmvcc : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc $$ []
  · iPkgInit
  ihave #Psync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  wp_auto
  wp_apply hClose r.wsp (v3rpc.wsIface r.srv.wsl) (v3rpc.wParams r.srv) r.γo $$ [$Hopen]
  · iframe #
  wp_apply wp_broadcast_chan_close r.cc r.γcc iprop(True) $$ [$Hcc] as -
  · iintro !>; itrivial
  wp_apply sync.join.WaitGroup.wp_Wait P n (v3rpc.swsF sws go!"wg") $$ [$Hadd] as -
  iapply HΦ
  itrivial

end proof

end EtcdGrove
end Perennial

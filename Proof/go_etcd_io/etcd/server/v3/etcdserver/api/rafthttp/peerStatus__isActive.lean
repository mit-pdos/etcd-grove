/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/rafthttp/peerStatus__isActive.lean`. Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.peerStatus__isActive


@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.api go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Assumptions]

theorem rafthttp.peerStatus.isActive.wp_proof :
    rafthttp.peerStatus.isActive.spec (GF := GF) (hG := hG) := by
  intro s
  wp_start as #Hs
  iunfold peerStatusOk at Hs
  icases Hs with ⟨%lg, %lid, %id, -, -, -, -, #Hmu⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  wp_apply wp_with_defer as %defer defer
  wp_apply sync.Mutex.wp_Lock _ (peerStatusInv s) $$ [$Hmu] as ⟨Hlocked, Hinv⟩
  iunfold peerStatusInv at Hinv
  icases Hinv with ⟨%a, %t, Ha, Ht⟩
  wp_auto
  wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Ha Ht]
  · inext
    iunfold peerStatusInv
    iexists _, _
    iframe
  iapply HΦ
  itrivial

end proof

end EtcdGrove
end Perennial

/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/rafthttp/newPeerStatus.lean`.
Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.newPeerStatus

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

theorem rafthttp.newPeerStatus.wp_proof :
    rafthttp.newPeerStatus.spec (GF := GF) (hG := hG) := by
  intro lg lid id Hlg
  wp_start as -
  wp_auto
  rw [_root_.decide_eq_false Hlg]
  wp_auto
  wp_alloc ps as Hps
  iStructNamed Hps
  ipersist lg; ipersist local'; ipersist id
  imod sync.init_Mutex (peerStatusInv ps) ⊤
    (ps.[rafthttp.peerStatus, go!"mu"]) $$ mu [active since] with #Hmu
  · inext
    iunfold peerStatusInv
    iexists _, _
    iframe
  (try wp_auto)
  iapply HΦ
  iunfold peerStatusOk
  iexists lg, lid, id
  iframe #
  ipureintro; exact Hlg

end proof

end EtcdGrove
end Perennial

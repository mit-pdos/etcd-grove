/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/rafthttp/isMsgSnap.lean`. Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.isMsgSnap
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetType

@[expose] public section

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

theorem rafthttp.isMsgSnap.wp_proof (hGetType : raftpb.Message.GetType.spec (GF := GF) (hG := hG)) :
    rafthttp.isMsgSnap.spec (GF := GF) (hG := hG) := by
  intro ml st
  wp_start as #Hm
  wp_auto
  wp_apply hGetType.1 ml DFrac.discard DFrac.discard false st $$ [$Hm] as -
  rw [show (MsgSnap : w32) = W32 7 from rfl]
  iapply HΦ
  itrivial

end proof

end EtcdGrove
end Perennial

module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRaftNode

@[expose] public section

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

example (tk tc : Loc) :
    {{ (structFieldRef time.Ticker go!"C" tk ↦□ tc : IProp GF) }}
      (App (Val (GoInstruction (GoLoad (go.GoType.ChannelType go.ChanDir.recvonly time.Time.ty))))
        (Val #(structFieldRef time.Ticker go!"C" tk)))
    {{ RET #tc; True }} := by
  wp_start as #H
  wp_auto
  iapply HΦ
  itrivial

end proof

end EtcdGrove
end Perennial

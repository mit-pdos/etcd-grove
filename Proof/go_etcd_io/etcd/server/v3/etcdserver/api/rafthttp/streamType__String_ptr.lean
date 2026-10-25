/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/rafthttp/streamType__String_ptr.lean`.
Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.streamType__String_ptr
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.streamType__String

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

theorem rafthttp.streamType.String_ptr.wp_proof
    (hString : rafthttp.streamType.String.spec (GF := GF) (hG := hG)) :
    rafthttp.streamType.String_ptr.spec (GF := GF) (hG := hG) := by
  intro p dq t
  wp_start as Hp
  wp_auto
  haveI : go.NotInterface go.string := ⟨by unfold go.string; trivial⟩
  (try wp_auto)
  wp_apply hString t as %s -
  iapply HΦ
  iexact Hp

end proof

end EtcdGrove
end Perennial

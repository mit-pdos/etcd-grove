/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__CommittedIndex.lean`. Lean-first (no Rocq
counterpart); the request path's unit 4b (2026-10-13).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__CommittedIndex
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__getCommittedIndex

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

theorem EtcdServer.CommittedIndex.wp_proof
    (hG' : EtcdServer.getCommittedIndex.spec (GF := GF) (hG := hG)) :
    EtcdServer.CommittedIndex.spec (GF := GF) (hG := hG) := by
  intro s γr
  wp_start as #Hinv
  wp_auto
  wp_apply hG' s γr none $$ [] as %v ⟨#Hv, -, -⟩
  · iframe #; iunfold srvCommittedOwnOpt; itrivial
  iapply HΦ
  iexact Hv

end proof

end EtcdGrove
end Perennial

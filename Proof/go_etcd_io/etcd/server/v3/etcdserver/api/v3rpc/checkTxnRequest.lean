/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart); the joint proof of
`checkRequestOp` and `checkTxnRequest` (Löb induction over nested transactions) is
`CheckLemmas.lean`'s.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.CheckLemmas

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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

theorem v3rpc.checkTxnRequest.wp_proof
    (hRange : v3rpc.checkRangeRequest.spec (GF := GF) (hG := hG))
    (hPut : v3rpc.checkPutRequest.spec (GF := GF) (hG := hG))
    (hDel : v3rpc.checkDeleteRequest.spec (GF := GF) (hG := hG)) :
    v3rpc.checkTxnRequest.spec (GF := GF) (hG := hG) :=
  v3rpc.checkTxnRequest_loeb hRange hPut hDel

end proof

end EtcdGrove
end Perennial

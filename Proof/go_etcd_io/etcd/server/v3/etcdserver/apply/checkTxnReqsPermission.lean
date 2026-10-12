/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.checkTxnReqsPermission
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.checkPutAuth
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.checkTxnPermission
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.AuthLemmas

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.apply go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]

theorem apply.checkTxnReqsPermission.wp_proof
    (hPut : apply.checkPutAuth.spec (GF := GF) (hG := hG))
    (hTxn : apply.checkTxnPermission.spec (GF := GF) (hG := hG)) :
    apply.checkTxnReqsPermission.spec (GF := GF) (hG := hG) := by
  intro st le γ P f ai info dq reqs ps ops
  iintro %Φ ⟨#Hpkg, #Hst, #Hle, Hai, #Hreqs, #Hops⟩ HΦ
  iapply (apply.checkTxnReqs_of hPut st le γ P f ai info dq reqs ps ops) $$ [Hai] HΦ
  iframe Hai
  iframe #
  iunfold apply.txnPermT
  imodintro
  iintro %rt %t %Φ' Hpre HΦ'
  iapply (hTxn st le γ P f ai info dq rt t) $$ Hpre HΦ'

end proof

end EtcdGrove
end Perennial

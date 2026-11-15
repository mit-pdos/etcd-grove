/-
Proof of the spec of the same name (the vertical slice's unit V2; as `quotaKVServer.Put`'s, unit P3b). Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.quotaKVServer__Txn
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.quotaAlarmer__check

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

theorem v3rpc.quotaKVServer.Txn.wp_proof
    (wp_check : v3rpc.quotaAlarmer.check.spec (GF := GF) (hG := hG)) :
    v3rpc.quotaKVServer.Txn.spec (GF := GF) (hG := hG) := by
  intro Req Rep Spec q s kv S m Φ' Ψe ci cd r
  wp_start_folded as ⟨#Hq, #Hh, HS, Hqr, #Hctx, #Hrc, #Hr, HSpec⟩
  rw [method_unfold (t := go.GoType.PointerType v3rpc.quotaKVServer.ty) (m := go!"Txn")]
  wp_call
  iunfold v3rpc.quotaKVServerAt at Hq
  icases Hq with ⟨%Hqn, #Hkv, #Hqa⟩
  wp_auto
  wp_apply wp_check _ s ci r (go.GoType.PointerType etcdserverpb.TxnRequest.ty) (Or.inr (Or.inl rfl))
    $$ [Hqr] as %err ⟨%Herr, Hqr⟩
  · iframe; iframe #
  cases err with
  | ok ei => cases Herr
  | nil =>
    iunfold v3rpc.quotaRd at Hqr
    icases Hqr with ⟨Hlg, Hbm⟩
    wp_auto
    iunfold grpcHandlerOkMd at Hh
    wp_apply Hh $$ %m %Φ' %Ψe %ci %cd %r [HS Hlg HSpec] as %resp %err' ⟨⟨HS, Hlg⟩, Hres, Hd, #Hse⟩
    · iframe; iframe #
    iapply HΦ
    iunfold v3rpc.quotaRd
    iframe
    iframe Hse

end proof

end EtcdGrove
end Perennial

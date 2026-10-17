/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3compactor/Periodic__getRetentions.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor.Periodic__getRetentions
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor.Periodic__getRetryInterval

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.api

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor.Assumptions]

theorem v3compactor.Periodic.getRetentions.wp_proof
    (wp_getRetryInterval : v3compactor.Periodic.getRetryInterval.spec (GF := GF) (hG := hG)) :
    v3compactor.Periodic.getRetentions.spec (GF := GF) (hG := hG) := by
  intro pc p dq
  unfold pdRetentions
  haveI : go.NotInterface go.int64 := ⟨by unfold go.int64; trivial⟩
  try simp only [_root_.Perennial.time.Hour, _root_.Perennial.time.Minute, go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor.retryDivisor] at *
  wp_start as ⟨Hp, %Hp10⟩
  wp_auto
  wp_apply wp_getRetryInterval $$ [$Hp] as Hp
  have hr : sint.Z (pdRetry p) ≠ 0 := pdRetry_ne_zero p Hp10
  rw [if_neg hr]
  wp_auto
  iapply HΦ
  iframe

end proof

end EtcdGrove
end Perennial

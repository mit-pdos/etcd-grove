/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3compactor/Periodic__getRetryInterval.lean`. Lean-first (no Rocq counterpart).
-/
module

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

theorem v3compactor.Periodic.getRetryInterval.wp_proof :
    v3compactor.Periodic.getRetryInterval.spec (GF := GF) (hG := hG) := by
  intro pc p dq
  unfold pdRetry pdCapped
  by_cases hc : sint.Z hourNs < sint.Z p <;> simp only [hc, ↓reduceIte]
  all_goals
    haveI : go.NotInterface go.int64 := ⟨by unfold go.int64; trivial⟩
    wp_start as Hp
    wp_auto
    wp_if_destruct
    all_goals
      try simp only [_root_.Perennial.time.Hour, go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor.retryDivisor]
      try wp_auto
      first
        | (exfalso; simp only [hourNs] at *; word)
        | (iapply HΦ; iframe)

end proof

end EtcdGrove
end Perennial

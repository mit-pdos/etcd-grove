/-
Proof of `Spec/go_etcd_io/etcd/api/v3/etcdserverpb/LeaseKeepAliveResponse__GetHeader.lean` (item 1,
the client lease). Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb.LeaseKeepAliveResponse__GetHeader

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

theorem LeaseKeepAliveResponse.GetHeader.wp_proof :
    LeaseKeepAliveResponse.GetHeader.spec (GF := GF) (hG := hG) := by
  intro x h dq
  wp_start as ⟨%Hnn, Hh⟩
  wp_auto
  wp_if_destruct
  · exact absurd rfl Hnn
  · try wp_auto
    iapply HΦ
    iexact Hh

end proof

end EtcdGrove
end Perennial

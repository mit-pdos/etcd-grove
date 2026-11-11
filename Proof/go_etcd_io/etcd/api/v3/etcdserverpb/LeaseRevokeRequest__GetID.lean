/-
Proof of `Spec/go_etcd_io/etcd/api/v3/etcdserverpb/LeaseRevokeRequest__GetID.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb.LeaseRevokeRequest__GetID

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.api.v3.etcdserverpb.Assumptions]

theorem LeaseRevokeRequest.GetID.wp_proof : LeaseRevokeRequest.GetID.spec (GF := GF) (hG := hG) := by
  intro p v dq
  wp_start as Hh
  wp_auto
  wp_if_destruct
  · wp_end
  · rw [ite_eq_right (by assumption)]; wp_end

end proof

end EtcdGrove
end Perennial

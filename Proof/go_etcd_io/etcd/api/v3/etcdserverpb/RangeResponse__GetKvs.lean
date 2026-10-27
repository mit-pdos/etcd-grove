/-
Proof of `Spec/go_etcd_io/etcd/api/v3/etcdserverpb/RangeResponse__GetKvs.lean`. Lean-first (no
Rocq counterpart); unit P4 (2026-10-14).
-/
module

public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb.RangeResponse__GetKvs

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

theorem RangeResponse.GetKvs.wp_proof : RangeResponse.GetKvs.spec (GF := GF) (hG := hG) := by
  intro r sl
  wp_start as ⟨%Hnn, #Hk⟩
  wp_auto
  wp_if_destruct
  · exact absurd rfl Hnn
  · wp_end

end proof

end EtcdGrove
end Perennial

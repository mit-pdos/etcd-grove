/-
Proof of `Spec/go_etcd_io/etcd/server/v3/lease/Lease__getRemainingTTL.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.lease.Lease__getRemainingTTL

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.lease lease

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.lease.Assumptions]

theorem lease.Lease.getRemainingTTL.wp_proof :
    lease.Lease.getRemainingTTL.spec (GF := GF) (hG := hG) := by
  intro l r t dq1 dq2
  wp_start as ⟨Hr, Ht⟩
  wp_auto
  wp_if_destruct
  · rw [if_pos (by word)]
    iapply HΦ; iframe
  · rw [if_neg (by word)]
    iapply HΦ; iframe

end proof

end EtcdGrove
end Perennial

/-
Proof of `Spec/go_etcd_io/etcd/server/v3/lease/lessor__isPrimary.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.lease.lessor__isPrimary

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

theorem lease.lessor.isPrimary.wp_proof : lease.lessor.isPrimary.spec (GF := GF) (hG := hG) := by
  intro lp dc dq
  wp_start as Hd
  wp_auto
  have h : (!decide (dc = chan.nil)) = decide (dc ≠ chan.nil) := by
    by_cases hd : dc = chan.nil <;> simp [hd]
  rw [h]
  iapply HΦ $$ Hd

end proof

end EtcdGrove
end Perennial

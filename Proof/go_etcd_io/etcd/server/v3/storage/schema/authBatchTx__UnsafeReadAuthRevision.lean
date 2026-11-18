/-
Proof of `Spec/go_etcd_io/etcd/server/v3/storage/schema/authBatchTx__UnsafeReadAuthRevision.lean`. Lean-first (no Rocq
counterpart); the authstore-noax stage (2026-11-18).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.schema.authBatchTx__UnsafeReadAuthRevision
public import Spec.go_etcd_io.etcd.server.v3.storage.schema.unsafeReadAuthRevision

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage backend

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [backend_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.schema.Assumptions]

theorem schema.authBatchTx.UnsafeReadAuthRevision.wp_proof
    (hF : schema.unsafeReadAuthRevision.spec (GF := GF) (hG := hG)) :
    schema.authBatchTx.UnsafeReadAuthRevision.spec (GF := GF) (hG := hG) := by
  intro atl rt H D hwf
  wp_start as ⟨#Htx, #Hrd, HH⟩
  wp_auto
  wp_apply (hF rt H D hwf) $$ [$Hrd $HH] as %x ⟨HH, %Hv⟩
  (try wp_auto)
  iapply HΦ
  iframe
  ipureintro; exact Hv

end proof

end EtcdGrove
end Perennial

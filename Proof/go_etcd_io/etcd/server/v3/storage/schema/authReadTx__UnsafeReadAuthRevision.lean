/-
Proof of `Spec/.../schema/authReadTx__UnsafeReadAuthRevision.lean`: `unsafeReadAuthRevision` on the transaction's fields. Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.schema.authReadTx__UnsafeReadAuthRevision
public import Spec.go_etcd_io.etcd.server.v3.storage.schema.unsafeReadAuthRevision

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.schema.Assumptions]

theorem schema.authReadTx.UnsafeReadAuthRevision.wp_proof
    (hF : schema.unsafeReadAuthRevision.spec (GF := GF) (hG := hG)) :
    schema.authReadTx.UnsafeReadAuthRevision.spec (GF := GF) (hG := hG) := by
  intro atx rt H D hwf
  wp_start as ⟨#Htx, #Hrd, HH⟩
  wp_auto
  wp_apply (hF rt H D hwf) $$ [$Hrd $HH] as %x ⟨HH, %Hx⟩
  (try wp_auto)
  iapply HΦ
  iframe
  ipureintro; exact Hx

end proof

end EtcdGrove
end Perennial

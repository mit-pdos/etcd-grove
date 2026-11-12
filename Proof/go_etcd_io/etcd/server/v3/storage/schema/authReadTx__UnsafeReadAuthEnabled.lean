/-
Proof of `Spec/.../schema/authReadTx__UnsafeReadAuthEnabled.lean`: `unsafeReadAuthEnabled` on the transaction's fields. Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.schema.authReadTx__UnsafeReadAuthEnabled
public import Spec.go_etcd_io.etcd.server.v3.storage.schema.unsafeReadAuthEnabled

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

theorem schema.authReadTx.UnsafeReadAuthEnabled.wp_proof
    (hF : schema.unsafeReadAuthEnabled.spec (GF := GF) (hG := hG)) :
    schema.authReadTx.UnsafeReadAuthEnabled.spec (GF := GF) (hG := hG) := by
  intro atx rt H D
  wp_start as ⟨#Htx, #Hrd, HH⟩
  wp_auto
  wp_apply (hF rt H D) $$ [$Hrd $HH] as %b ⟨HH, %Hb⟩
  (try wp_auto)
  iapply HΦ
  iframe
  ipureintro; exact Hb

end proof

end EtcdGrove
end Perennial

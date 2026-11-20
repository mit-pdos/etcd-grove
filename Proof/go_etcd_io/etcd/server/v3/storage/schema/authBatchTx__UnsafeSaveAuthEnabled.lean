/-
Proof of `Spec/.../schema/authBatchTx__UnsafeSaveAuthEnabled.lean`: one call of the transaction. Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.schema.authBatchTx__UnsafeSaveAuthEnabled

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

theorem schema.authBatchTx.UnsafeSaveAuthEnabled.wp_proof :
    schema.authBatchTx.UnsafeSaveAuthEnabled.spec (GF := GF) (hG := hG) := by
  intro atx t b R Q
  unfold schema.authEnabledKey
  wp_start_folded as ⟨#Htx, HR, #HP⟩
  rw [MethodUnfold.method_unfold (t := go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.schema.authBatchTx.ty) (m := go!"UnsafeSaveAuthEnabled")]
  wp_call
  ihave Hsi : (schema.schemaInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hsi with ⟨-, -, -, -, -, -, -, ⟨%ab, #HA, -⟩, -, -, ⟨%ks, #HK, #Hks⟩, -, ⟨%es, #HE, #Hes⟩, ⟨%ds, #HD, #Hds⟩, -⟩
  wp_auto
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte]
    (try wp_auto)
    (try wp_auto)
    wp_bind (App (App (App (Val #(methods t.ty _ t.v)) _) _) _)
    iapply HP $$ %ab %ks %ds [$HA $Hks $Hds $HR]
    inext
    iintro HQ
    (try wp_auto)
    iapply HΦ
    iexact HQ
  · simp only [↓reduceIte]
    (try wp_auto)
    (try wp_auto)
    wp_bind (App (App (App (Val #(methods t.ty _ t.v)) _) _) _)
    iapply HP $$ %ab %ks %es [$HA $Hks $Hes $HR]
    inext
    iintro HQ
    (try wp_auto)
    iapply HΦ
    iexact HQ

end proof

end EtcdGrove
end Perennial

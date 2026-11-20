/-
Proof of `Spec/.../schema/authBatchTx__UnsafeDeleteUser.lean`: one call of the transaction. Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.schema.authBatchTx__UnsafeDeleteUser

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

theorem schema.authBatchTx.UnsafeDeleteUser.wp_proof :
    schema.authBatchTx.UnsafeDeleteUser.spec (GF := GF) (hG := hG) := by
  intro atx t name R Q
  wp_start_folded as ⟨#Htx, HR, #HD⟩
  rw [MethodUnfold.method_unfold (t := go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.schema.authBatchTx.ty) (m := go!"UnsafeDeleteUser")]
  wp_call
  ihave Hsi : (schema.schemaInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hsi with ⟨-, -, -, -, -, -, -, -, ⟨%ub, #HB, -⟩, -⟩
  wp_auto
  wp_apply wp_string_to_bytes name as %key ⟨Hkey, -⟩
  (try wp_auto)
  wp_bind (App (App (Val #(methods t.ty _ t.v)) _) _)
  iapply HD $$ %ub %key [$HB $Hkey $HR]
  inext
  iintro HQ
  (try wp_auto)
  iapply HΦ
  iexact HQ

end proof

end EtcdGrove
end Perennial

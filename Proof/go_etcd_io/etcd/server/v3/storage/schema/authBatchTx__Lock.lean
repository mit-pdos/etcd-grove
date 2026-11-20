/-
Proof of `Spec/.../schema/authBatchTx__Lock.lean`: one call of the transaction. Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.schema.authBatchTx__Lock

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

theorem schema.authBatchTx.Lock.wp_proof :
    schema.authBatchTx.Lock.spec (GF := GF) (hG := hG) := by
  intro atx t R Q
  wp_start_folded as ⟨#Htx, HR, #HL⟩
  rw [MethodUnfold.method_unfold (t := go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.schema.authBatchTx.ty) (m := go!"Lock")]
  wp_call
  wp_auto
  (try wp_auto)
  wp_bind (App (Val #(methods t.ty go!"LockInsideApply" t.v)) (Val #()))
  iapply HL $$ HR
  inext
  iintro HQ
  (try wp_auto)
  iapply HΦ
  iexact HQ

end proof

end EtcdGrove
end Perennial

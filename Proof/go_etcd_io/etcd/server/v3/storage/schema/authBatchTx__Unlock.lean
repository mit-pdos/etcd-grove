/-
Proof of `Spec/.../schema/authBatchTx__Unlock.lean`: two calls of the transaction. Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.schema.authBatchTx__Unlock

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

theorem schema.authBatchTx.Unlock.wp_proof :
    schema.authBatchTx.Unlock.spec (GF := GF) (hG := hG) := by
  intro atx t R C Q
  wp_start_folded as ⟨#Htx, HR, #HU, #HC⟩
  rw [MethodUnfold.method_unfold (t := go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.schema.authBatchTx.ty) (m := go!"Unlock")]
  wp_call
  (try wp_auto)
  wp_bind (App (Val #(methods t.ty go!"Unlock" t.v)) (Val #()))
  iapply HU $$ HR
  inext
  iintro HC'
  (try wp_auto)
  wp_bind (App (Val #(methods t.ty go!"Commit" t.v)) (Val #()))
  iapply HC $$ HC'
  inext
  iintro HQ
  (try wp_auto)
  iapply HΦ
  iexact HQ

end proof

end EtcdGrove
end Perennial

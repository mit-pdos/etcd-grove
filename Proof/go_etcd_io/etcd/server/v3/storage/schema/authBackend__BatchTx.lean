/-
Proof of `Spec/.../schema/authBackend__BatchTx.lean`: the backend's `BatchTx`, a new `*authBatchTx`. Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.schema.authBackend__BatchTx

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

theorem schema.authBackend.BatchTx.wp_proof :
    schema.authBackend.BatchTx.spec (GF := GF) (hG := hG) := by
  intro abe bi lg C
  wp_start_folded as ⟨#Hbe, #Hlg, #HB⟩
  rw [MethodUnfold.method_unfold (t := go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.schema.authBackend.ty) (m := go!"BatchTx")]
  wp_call
  (try wp_auto)
  wp_bind (App (Val #(methods bi.ty go!"BatchTx" bi.v)) (Val #()))
  iapply HB $$ []
  · itrivial
  inext
  iintro %tx ⟨%t, %Ht, HC⟩
  subst Ht
  (try wp_auto)
  wp_alloc l as Hl
  iStructNamed Hl
  ipersist tx
  ipersist lg
  wp_auto
  iapply HΦ
  iexists l, t
  iframe # HC
  ipureintro; rfl

end proof

end EtcdGrove
end Perennial

/-
Proof of `Spec/.../schema/authBackend__ForceCommit.lean`: one call of the backend. Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.schema.authBackend__ForceCommit

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

theorem schema.authBackend.ForceCommit.wp_proof :
    schema.authBackend.ForceCommit.spec (GF := GF) (hG := hG) := by
  intro abe bi R Q
  wp_start_folded as ⟨#Hbe, HR, #HF⟩
  rw [MethodUnfold.method_unfold (t := go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.schema.authBackend.ty) (m := go!"ForceCommit")]
  wp_call
  (try wp_auto)
  wp_bind (App (Val #(methods bi.ty go!"ForceCommit" bi.v)) (Val #()))
  iapply HF $$ HR
  inext
  iintro HQ
  (try wp_auto)
  iapply HΦ
  iexact HQ

end proof

end EtcdGrove
end Perennial

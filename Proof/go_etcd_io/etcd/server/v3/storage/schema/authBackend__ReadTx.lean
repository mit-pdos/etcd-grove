/-
Proof of `Spec/.../schema/authBackend__ReadTx.lean`: the backend's `ReadTx()` (its contract) in a new `authReadTx`. Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.schema.authBackend__ReadTx

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

theorem schema.authBackend.ReadTx.wp_proof :
    schema.authBackend.ReadTx.spec (GF := GF) (hG := hG) := by
  intro abe bi lg R Held
  wp_start as ⟨#Hbe, #Hlg, #HBE⟩
  iunfold schema.authBE at HBE
  wp_auto
  wp_apply HBE as %tx Htx
  icases Htx with ⟨%rti, %Hrti, #Hrtx⟩
  subst Hrti
  wp_alloc l as Hl
  iStructNamed Hl
  ipersist tx
  ipersist lg
  wp_auto
  iapply HΦ
  iexists l, rti
  iframe #
  ipureintro; rfl

end proof

end EtcdGrove
end Perennial

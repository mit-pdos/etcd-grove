/-
Proof of `Spec/.../schema/authBatchTx__UnsafeGetAllUsers.lean`: `unsafeGetAllUsers` on the transaction's fields. Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.schema.authBatchTx__UnsafeGetAllUsers
public import Spec.go_etcd_io.etcd.server.v3.storage.schema.unsafeGetAllUsers

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

theorem schema.authBatchTx.UnsafeGetAllUsers.wp_proof
    (hF : schema.unsafeGetAllUsers.spec (GF := GF) (hG := hG)) :
    schema.authBatchTx.UnsafeGetAllUsers.spec (GF := GF) (hG := hG) := by
  intro atx t lg H D dU hwf
  wp_start as ⟨#Htx, #Hlg, #Hrd, HH⟩
  wp_auto
  wp_apply (hF lg t H D dU hwf) $$ [$Hrd $HH] as %s ⟨HH, Hs⟩
  (try wp_auto)
  iapply HΦ
  iframe

end proof

end EtcdGrove
end Perennial

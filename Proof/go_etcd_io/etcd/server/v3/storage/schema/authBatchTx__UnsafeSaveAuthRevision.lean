/-
Proof of `Spec/.../schema/authBatchTx__UnsafeSaveAuthRevision.lean`: `PutUint64` into a fresh slice, one call of the transaction. Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.schema.authBatchTx__UnsafeSaveAuthRevision
public import Spec.encoding.binary.bigEndian__PutUint64

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

theorem schema.authBatchTx.UnsafeSaveAuthRevision.wp_proof
    (hP : binary.bigEndian.PutUint64.spec (GF := GF) (hG := hG)) :
    schema.authBatchTx.UnsafeSaveAuthRevision.spec (GF := GF) (hG := hG) := by
  intro atx t rev R Q
  unfold schema.authRevisionKey
  wp_start_folded as ⟨#Htx, HR, #HP⟩
  rw [MethodUnfold.method_unfold (t := go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.schema.authBatchTx.ty) (m := go!"UnsafeSaveAuthRevision")]
  wp_call
  ihave Hsi : (schema.schemaInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hsi with ⟨-, -, -, -, -, -, -, ⟨%ab, #HA, -⟩, -, -, -, ⟨%ks, #HK, #Hks⟩, -⟩
  wp_auto
  wp_apply (wp_slice_make2 (V := w8) (t := go.byte)) as %bs ⟨Hbs, -⟩
  · ipureintro; decide
  wp_apply wp_bePutUint64 hP bs _ rev (by simp) $$ [$Hbs] as Hbs
  imod ownSlice_persist $$ Hbs with #Hbs
  (try wp_auto)
  wp_bind (App (App (App (Val #(methods t.ty _ t.v)) _) _) _)
  iapply HP $$ %ab %ks %bs [$HA $Hks $Hbs $HR]
  inext
  iintro HQ
  (try wp_auto)
  iapply HΦ
  iexact HQ

end proof

end EtcdGrove
end Perennial

/-
Proof of `Spec/go_etcd_io/etcd/server/v3/storage/schema/UnsafeDeleteLease.lean`.
Lean-first (no Rocq counterpart). (The lessor-noax stage, 2026-11-18) translated with its body;
until then the trust boundary (names-only).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.schema.UnsafeDeleteLease
public import Spec.go_etcd_io.etcd.server.v3.storage.schema.leaseIDToBytes

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

theorem schema.UnsafeDeleteLease.wp_proof
    (hK : schema.leaseIDToBytes.spec (GF := GF) (hG := hG)) :
    schema.UnsafeDeleteLease.spec (GF := GF) (hG := hG) := by
  intro tx lpb dq v bk R Q
  wp_start as ⟨#Hbk, Hl, HR, #HD⟩
  icases typedPointsto_not_null_dup _ _ _ $$ Hl with ⟨Hl, %Hnn⟩
  iStructNamed Hl
  wp_auto
  wp_apply hK as %key Hkey
  imod ownSlice_persist key _ _ $$ Hkey with #Hkey
  (try wp_auto)
  wp_bind (App (App (Val #(methods tx.ty _ tx.v)) (Val #bk)) (Val #key))
  iapply HD $$ %key [HR]
  · iframe HR Hkey
  inext
  iintro HQ
  (try wp_auto)
  iapply HΦ
  iframe HQ
  iapply typedPointsto_combine _ _ _ Hnn
  simp only [TypedPointsto.typedPointstoDef]
  iframe

end proof

end EtcdGrove
end Perennial

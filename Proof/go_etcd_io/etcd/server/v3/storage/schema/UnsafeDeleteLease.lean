/-
Proof of `Spec/go_etcd_io/etcd/server/v3/storage/schema/UnsafeDeleteLease.lean` (2026-11-19: the
trust boundary until then, names-only). Lean-first (no Rocq counterpart).
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
    (hB : schema.leaseIDToBytes.spec (GF := GF) (hG := hG)) :
    schema.UnsafeDeleteLease.spec (GF := GF) (hG := hG) := by
  intro tx lpb dq v bk R Q
  wp_start as ⟨#Hbk, Hl, HR, #HDel⟩
  icases typedPointsto_not_null_dup _ _ _ $$ Hl with ⟨Hl, %Hnn⟩
  iStructNamedPrefix Hl "l"
  wp_auto
  wp_apply hB as %key Hkey
  ipersist Hkey
  wp_bind (App (App (Val #(methods tx.ty go!"UnsafeDelete" tx.v)) (Val #bk)) (Val #key))
  iapply HDel $$ [HR]
  · iframe HR
    iexact Hkey
  inext
  iintro HQ
  wp_auto
  iapply HΦ
  iframe HQ
  iapply typedPointsto_combine _ _ _ Hnn
  simp only [TypedPointsto.typedPointstoDef]
  iframe

end proof

end EtcdGrove
end Perennial

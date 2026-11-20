/-
Proof of `Spec/.../schema/authBackend__CreateAuthBuckets.lean`: the backend's `BatchTx`, `LockOutsideApply`, three `UnsafeCreateBucket`, the deferred `Unlock`. Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.schema.authBackend__CreateAuthBuckets

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

theorem schema.authBackend.CreateAuthBuckets.wp_proof :
    schema.authBackend.CreateAuthBuckets.spec (GF := GF) (hG := hG) := by
  intro abe bi R L Q
  wp_start_folded as ⟨#Hbe, HR, #HB⟩
  rw [MethodUnfold.method_unfold (t := go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.schema.authBackend.ty) (m := go!"CreateAuthBuckets")]
  wp_call
  ihave Hsi : (schema.schemaInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hsi with ⟨-, -, -, -, -, -, -, ⟨%b0, #HA0, -⟩, ⟨%b1, #HA1, -⟩, ⟨%b2, #HA2, -⟩, -⟩
  wp_auto
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_bind (App (Val #(methods bi.ty go!"BatchTx" bi.v)) (Val #()))
  iapply HB $$ []
  · itrivial
  inext
  iintro %tx ⟨%t, %Ht, #HL, #H0, #H1, #H2, #HU⟩
  subst Ht
  (try wp_auto)
  wp_bind (App (Val #(methods t.ty go!"LockOutsideApply" t.v)) (Val #()))
  iapply HL $$ HR
  inext
  iintro HL0
  (try wp_auto)
  wp_bind (App (Val #(methods t.ty go!"UnsafeCreateBucket" t.v)) (Val #b0))
  iapply H0 $$ %b0 [$HL0 $HA0]
  inext
  iintro HL1
  (try wp_auto)
  wp_bind (App (Val #(methods t.ty go!"UnsafeCreateBucket" t.v)) (Val #b1))
  iapply H1 $$ %b1 [$HL1 $HA1]
  inext
  iintro HL2
  (try wp_auto)
  wp_bind (App (Val #(methods t.ty go!"UnsafeCreateBucket" t.v)) (Val #b2))
  iapply H2 $$ %b2 [$HL2 $HA2]
  inext
  iintro HL3
  (try wp_auto)
  wp_bind (App (Val #(methods t.ty go!"Unlock" t.v)) (Val #()))
  iapply HU $$ HL3
  inext
  iintro HQ
  (try wp_auto)
  iapply HΦ
  iexact HQ

end proof

end EtcdGrove
end Perennial

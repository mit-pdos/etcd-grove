/-
Proof of `Spec/.../schema/authBackend__GetAllRoles.lean`: `BatchTx`, `Lock`, `UnsafeGetAllRoles`, the deferred `Unlock`. Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.schema.authBackend__GetAllRoles
public import Spec.go_etcd_io.etcd.server.v3.storage.schema.authBackend__BatchTx
public import Spec.go_etcd_io.etcd.server.v3.storage.schema.authBatchTx__Lock
public import Spec.go_etcd_io.etcd.server.v3.storage.schema.authBatchTx__UnsafeGetAllRoles
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

theorem schema.authBackend.GetAllRoles.wp_proof
    (hBT : schema.authBackend.BatchTx.spec (GF := GF) (hG := hG))
    (hL : schema.authBatchTx.Lock.spec (GF := GF) (hG := hG))
    (hR : schema.authBatchTx.UnsafeGetAllRoles.spec (GF := GF) (hG := hG))
    (hU : schema.authBatchTx.Unlock.spec (GF := GF) (hG := hG)) :
    schema.authBackend.GetAllRoles.spec (GF := GF) (hG := hG) := by
  intro abe bi lg R Lk C Q
  wp_start_folded as ⟨#Hbe, #Hlg, HR, #HB⟩
  rw [MethodUnfold.method_unfold (t := go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.schema.authBackend.ty) (m := go!"GetAllRoles")]
  wp_call
  wp_auto
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply (hBT abe bi lg (fun t => iprop(
      ({{ R }} (App (Val #(methods t.ty go!"LockInsideApply" t.v)) (Val #()))
        {{ RET #(); ∃ m : backend.BktData, ⌜schema.rolesWf m⌝ ∗ Lk m }}) ∗
      (∀ m : backend.BktData, □ schema.authRolesRange t (Lk m) m) ∗
      (∀ m : backend.BktData, {{ Lk m }} (App (Val #(methods t.ty go!"Unlock" t.v)) (Val #())) {{ RET #(); C m }}) ∗
      (∀ m : backend.BktData, {{ C m }} (App (Val #(methods t.ty go!"Commit" t.v)) (Val #())) {{ RET #(); Q m }})))) $$
    [$Hbe $Hlg $HB] as %tx ⟨%l, %t, %Htx, #Htxf, #Hlgf, #HL, #HRR, #HU, #HC⟩
  subst Htx
  (try wp_auto)
  wp_apply (hL l t R iprop(∃ m : backend.BktData, ⌜schema.rolesWf m⌝ ∗ Lk m)) $$ [$Htxf $HR $HL]
    as ⟨%m, %Hwf, HLk⟩
  ihave #HRm := HRR $$ %m
  wp_apply (hR l t lg (Lk m) m Hwf) $$ [$Htxf $Hlgf $HRm $HLk] as %s ⟨HLk, Hs⟩
  (try wp_auto)
  wp_bind (App (Val (l @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.schema.authBatchTx.ty @!! go!"Unlock")) (Val #()))
  iapply (hU l t (Lk m) (C m) (Q m)) $$ [Hpkg Htxf HLk]
  · iframe Hpkg Htxf HLk
    isplitl []
    · iexact HU
    · iexact HC
  inext
  iintro HQ
  (try wp_auto)
  iapply HΦ
  iexists m
  iframe HQ Hs

end proof

end EtcdGrove
end Perennial

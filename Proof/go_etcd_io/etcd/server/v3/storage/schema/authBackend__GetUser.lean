/-
Proof of `Spec/.../schema/authBackend__GetUser.lean`: `ReadTx`, `RLock`, `UnsafeGetUser`, the deferred `RUnlock`. Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.schema.authBackend__GetUser
public import Spec.go_etcd_io.etcd.server.v3.storage.schema.authBackend__ReadTx
public import Spec.go_etcd_io.etcd.server.v3.storage.schema.authReadTx__RLock
public import Spec.go_etcd_io.etcd.server.v3.storage.schema.authReadTx__UnsafeGetUser
public import Spec.go_etcd_io.etcd.server.v3.storage.schema.authReadTx__RUnlock

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.schema.Assumptions]

theorem schema.authBackend.GetUser.wp_proof
    (hRT : schema.authBackend.ReadTx.spec (GF := GF) (hG := hG))
    (hRL : schema.authReadTx.RLock.spec (GF := GF) (hG := hG))
    (hG_ : schema.authReadTx.UnsafeGetUser.spec (GF := GF) (hG := hG))
    (hRU : schema.authReadTx.RUnlock.spec (GF := GF) (hG := hG)) :
    schema.authBackend.GetUser.spec (GF := GF) (hG := hG) := by
  intro abe bi lg R Held name
  wp_start as ⟨#Hbe, #Hlg, %Hlgnn, #HBE, HR⟩
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply (hRT abe bi lg R Held) $$ [$Hbe $Hlg $HBE] as %tx ⟨%l, %rt, %Htx, #Htxf, #Hlgf, #Hrtx⟩
  subst Htx
  (try wp_auto)
  wp_apply (hRL l rt R Held) $$ [$Htxf $Hrtx $HR] as ⟨%D, %Hwf, HD, #HrdD⟩
  (try wp_auto)
  wp_apply (hG_ l rt lg name (Held D) D Hlgnn Hwf.1) $$ [$Htxf $Hlgf $HrdD $HD] as %u ⟨HD, Hu⟩
  imod (schema.userOutDX_persist _ _ _) $$ Hu with Hu
  (try wp_auto)
  wp_bind (App (Val (l @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.schema.authReadTx.ty @!! go!"RUnlock")) (Val #()))
  -- `iapply`, not `wp_apply`: a Lean spec applied at the deferred call leaves a stray goal
  iapply (hRU l rt R Held D) $$ [Hpkg Htxf Hrtx HD]
  · iframe Hpkg Htxf Hrtx HD
  inext
  iintro HR
  (try wp_auto)
  iapply HΦ
  iframe HR
  iexists D
  iframe Hu
  ipureintro; exact Hwf

end proof

end EtcdGrove
end Perennial

/-
Proof of `Spec/go_etcd_io/etcd/server/v3/auth/authStore__Revision.lean`. Lean-first (no Rocq counterpart;
unit P2).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__Revision

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.auth auth

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

theorem auth.authStore.Revision.wp_proof :
    auth.authStore.Revision.spec (GF := GF) (hG := hG) := by
  intro st R M
  wp_start as #Hinv
  ihave #Hatomic : isPkgInit (PROP := IProp GF) pkg_id.sync.atomic $$ []
  · iPkgInit
  iunfold authInv at Hinv
  icases Hinv with ⟨%Hst, #Hrev, -⟩
  wp_auto
  wp_apply_core sync.atomic.wp_LoadUint64 $$ [] [HΦ]
  · iexact Hatomic
  iinv Hrev with Hi Hclose
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iunfold revInv at Hi
  icases Hi with ⟨%r, Hr⟩
  iexists r
  iframe Hr
  iintro Hr
  imod Hmask with -
  imod Hclose $$ [Hr] with -
  · inext; iunfold revInv; iexists r; iexact Hr
  imodintro
  wp_auto
  iapply HΦ
  ipureintro; trivial

end proof

end EtcdGrove
end Perennial

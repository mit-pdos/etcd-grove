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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

theorem auth.authStore.Revision.wp_proof :
    auth.authStore.Revision.spec (GF := GF) (hG := hG) := by
  intro st R M hsO
  wp_start as ⟨#Hinv, Hown⟩
  ihave #Hatomic : isPkgInit (PROP := IProp GF) pkg_id.sync.atomic $$ []
  · iPkgInit
  iunfold authInv at Hinv
  icases Hinv with ⟨%Hst, #Hrev, -⟩
  wp_auto
  wp_apply_core sync.atomic.wp_LoadUint64 $$ [] [HΦ Hown]
  · iexact Hatomic
  iinv Hrev with Hi Hclose
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iunfold revInv at Hi
  icases Hi with ⟨%r, Hr, #Hv, Hc⟩
  iexists r
  iframe Hr
  iintro Hr
  -- with the authority, the value is the latest state's revision
  ihave Hag : iprop(authOwnOpt M hsO ∗ revCur M r ∗
      ⌜∀ (hs : List AuthState) (stl : AuthState), hsO = some hs → histLast M hs stl →
        M.isOn = true → M ≠ .any → uint.nat r = stl.revision⌝) $$ [Hown Hc]
  · cases hsO with
    | none => iframe Hown Hc; ipureintro; intro _ _ h; cases h
    | some hs =>
      iunfold authOwnOpt at Hown
      ihave H := revCur_agree_own M hs r $$ Hown Hc
      icases H with ⟨Hown, Hc, %Hp⟩
      iunfold authOwnOpt
      iframe Hown Hc
      ipureintro; intro hs' stl h; cases h; exact Hp stl
  icases Hag with ⟨Hown, Hc, %Hp⟩
  imod Hmask with -
  imod Hclose $$ [Hr Hc] with -
  · inext; iunfold revInv; iexists r; iframe Hr Hc; iexact Hv
  imodintro
  wp_auto
  iapply HΦ
  iframe Hown
  iframe Hv
  ipureintro; exact Hp

end proof

end EtcdGrove
end Perennial

/-
Proof of the spec of the same name (the auth plan's S4, 2026-10-24). Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__commitRevision
public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__Revision

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.auth auth go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

theorem auth.authStore.commitRevision.wp_proof
    (h_Revision : auth.authStore.Revision.spec (GF := GF) (hG := hG)) :
    auth.authStore.commitRevision.spec (GF := GF) (hG := hG) := by
  intro st R M P f T ti Lk sta X hs st0
  wp_start as ⟨#Hinv, #Hlk, HLk, Hown, %Hp⟩
  obtain ⟨Hlast, Hsrev, Hfit, Hk, Hoff⟩ := Hp
  ihave #Hatomic : isPkgInit (PROP := IProp GF) pkg_id.sync.atomic $$ []
  · iPkgInit
  ihave #Hinv' := Hinv
  iunfold authInv at Hinv'
  icases Hinv' with ⟨%Hst, #Hrevinv, -⟩
  ihave #Hlk' := Hlk
  iunfold authBatchTxLk at Hlk'
  icases Hlk' with ⟨-, -, -, -, -, -, -, #HSaveRev, -⟩
  wp_auto
  wp_apply_core sync.atomic.wp_AddUint64 $$ [] [-Hatomic]
  · iexact Hatomic
  iinv Hrevinv with Hi Hclose
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iunfold revInv at Hi
  icases Hi with ⟨%r, Hr, -, Hc⟩
  iexists r
  iframe Hr
  iintro Hr
  -- the atomic's old value is the latest state's revision (`on γa`); the step's state appended
  ihave H := revCur_agree M hs r $$ Hown Hc
  icases H with ⟨Hown, Hc, %Hagree⟩
  have hr' : M.isOn = true → M ≠ .any → uint.nat (r + W64 1) = (bump sta).revision := by
    intro h1 h2
    have := Hagree st0 Hlast h1 h2
    simp only [bump]
    rw [← Hsrev] at this
    word
  imod (authOwnF_revCur_append M hs (bump sta) r (r + W64 1) Hk (fun h => by
      subst h; exact Hoff rfl) hr') $$ Hown Hc with ⟨Hown, Hc, #Hv⟩
  imod Hmask with -
  imod Hclose $$ [Hr Hc] with -
  · inext; iunfold revInv; iexists (r + W64 1); iframe Hr Hc; iexact Hv
  imodintro
  wp_auto
  icases (authOwnF_split M (hs ++ [bump sta])).1 $$ Hown with ⟨Hown, Hsh⟩
  ihave Hown' : authOwnOpt M (some (hs ++ [bump sta])) $$ [Hown]
  · rw [authOwnOpt_some]; iexact Hown
  wp_apply (h_Revision st R M (some (hs ++ [bump sta]))) $$ [$Hinv $Hown'] as %x ⟨Hown', -, %Hx⟩
  simp only [authOwnOpt_some]
  ihave Hown' := (authOwnF_split M (hs ++ [bump sta])).2 $$ [Hown' Hsh]
  · iframe Hown' Hsh
  wp_bind (App (Val #(methods ti.ty go!"UnsafeSaveAuthRevision" ti.v)) (Val #x))
  iapply HSaveRev $$ %sta %X %x HLk
  inext
  iintro HLk
  wp_auto
  iapply HΦ
  iexists (uint.nat x)
  iframe HLk Hown'
  ipureintro
  cases M with
  | on γa =>
    simp only [revAfter]
    have := Hx (hs ++ [bump sta]) (bump sta) rfl (by simp [histLast]) rfl (by intro h; cases h)
    rw [this]; rfl
  | off => trivial
  | any => trivial


end proof

end EtcdGrove
end Perennial

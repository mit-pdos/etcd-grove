/-
Proof of the spec of the same name (the auth plan's S4, 2026-10-24). Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__setRevision

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.auth auth go_etcd_io.etcd.api.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

theorem auth.authStore.setRevision.wp_proof :
    auth.authStore.setRevision.spec (GF := GF) (hG := hG) := by
  intro st R M rev hs N opt stl
  wp_start as ⟨#Hinv, Hown, Hsh, #Hcap, %Hp⟩
  obtain ⟨Hlast, Hrev, Hoptlen, HN, Hopt⟩ := Hp
  ihave #Hatomic : isPkgInit (PROP := IProp GF) pkg_id.sync.atomic $$ []
  · iPkgInit
  ihave #Hinv' := Hinv
  iunfold authInv at Hinv'
  icases Hinv' with ⟨%Hst, #Hrevinv, -⟩
  wp_auto
  wp_apply_core sync.atomic.wp_StoreUint64 $$ [] [HΦ Hown Hsh]
  · iexact Hatomic
  iinv Hrevinv with Hi Hclose
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iunfold revInv at Hi
  icases Hi with ⟨%r, Hr, -, Hc, Hf⟩
  iexists r
  iframe Hr
  iintro Hr
  -- the authority after the optional append, the atomic at the latest revision
  ihave Hg : iprop(|==> (authOwn M (hs ++ N ++ opt) ∗
      (if opt.isEmpty then iprop(True) else authLockShare M (hs ++ N ++ opt)) ∗
      revCur M rev ∗ revisionVerdict M rev)) $$ [Hown Hsh Hc]
  · cases opt with
    | nil =>
      simp only [List.append_nil, List.isEmpty_nil, ↓reduceIte] at Hlast ⊢
      imod (authOwnPM_revCur_set M hs N stl r rev Hlast (fun _ _ => Hrev)) $$ Hown Hc
        with ⟨Hown, Hc, #Hv⟩
      imodintro
      iframe Hown Hc Hv
    | cons x xs =>
      have hx : xs = [] := by
        cases xs with
        | nil => rfl
        | cons _ _ => simp at Hoptlen
      subst hx
      have hN : N = [] := by
        cases N with
        | nil => rfl
        | cons y ys => exact absurd (HN (by simp)) (by simp)
      subst hN
      simp only [List.append_nil, List.nil_append, List.isEmpty_cons, Bool.false_eq_true,
        ↓reduceIte] at Hlast ⊢
      have hxr : M.isOn = true → M ≠ .any → uint.nat rev = x.revision := by
        intro h1 h2
        cases M with
        | on γa =>
          simp only [histLast, List.getLast?_append, List.getLast?_singleton, Option.some_or] at Hlast
          cases Hlast; exact Hrev
        | off => cases h1
        | any => exact absurd rfl h2
      obtain ⟨hk, hoff⟩ := Hopt x (List.mem_singleton.2 rfl)
      ihave Hown := (authOwnPM_nil M hs).1 $$ Hown
      ihave HF := (authOwnF_split M hs).2 $$ [Hown Hsh]
      · iframe Hown Hsh
      imod (authOwnF_revCur_append M hs x r rev hk hoff hxr) $$ HF Hc [Hcap] with ⟨HF, Hc, #Hv⟩
      · iapply Hcap; ipureintro; exact List.mem_singleton.2 rfl
      icases (authOwnF_split M (hs ++ [x])).1 $$ HF with ⟨Hown, Hsh⟩
      imodintro
      iframe Hown Hsh Hc Hv
  imod Hg with ⟨Hown, Hsh, Hc, #Hv⟩
  imod (authOwn_revFresh M (hs ++ N ++ opt) stl r rev (fun γa h => by subst h; exact Hlast)
    (fun _ _ => Hrev)) $$ Hown Hf with ⟨Hown, Hf⟩
  imod Hmask with -
  imod Hclose $$ [Hr Hc Hf] with -
  · inext; iunfold revInv; iexists rev; iframe Hr Hc Hf; iexact Hv
  imodintro
  wp_auto
  iapply HΦ
  iframe Hown Hsh

end proof

end EtcdGrove
end Perennial

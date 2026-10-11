/-
Proof of `Spec/go_etcd_io/etcd/client/v3/experimental/recipes/newUniqueKV.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.experimental.recipes.newUniqueKV
public import Spec.go_etcd_io.etcd.client.v3.experimental.recipes.putNewKV
public import Perennial.Proof.time

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace recipes

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.client.v3.experimental.recipes go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.experimental.recipes.Assumptions]

theorem newUniqueKV.wp_proof (hPNK : putNewKV.spec (GF := GF) (hG := hG)) :
    newUniqueKV.spec (GF := GF) (hG := hG) := by
  intro kv pfx kp val lo
  wp_start as ⟨#Hkv, #Hlo, %Hk⟩
  ihave Hri : (recipesInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hri with ⟨⟨%eK, #HeK, %HeKl⟩, -, -, -⟩
  ihave #Hfmt : isPkgInit (PROP := IProp GF) pkg_id.fmt $$ []
  · iPkgInit
  ihave #Herr : isPkgInit (PROP := IProp GF) pkg_id.errors $$ []
  · iPkgInit
  wp_auto
  irename «prefix» => Hprefix
  ihave IH : iprop("Hkvp" ∷ kv_ptr ↦ GoInterface.ok kv ∗ "Hpre" ∷ prefix_ptr ↦ kp ∗
      "Hval" ∷ val_ptr ↦ val) $$ [kv Hprefix val]
  · iframe
  wp_for IH
  wp_apply time.wp_Now as %t -
  wp_apply time.Time.wp_UnixNano' t as %x -
  (try wp_auto)
  wp_apply wp_slice_literal
  try (isplitr; (ipureintro; rfl))
  iintro %sla ⟨Hargs, -⟩
  (try wp_auto)
  wp_apply _root_.Perennial.fmt.wp_Sprintf _ _ _ _ ?wf $$ [$Hfmt $Hargs] as %key ⟨-, %Hkey⟩
  case wf =>
    exact .cons_string _ _ (.cons_int _ _ _ (.int64 x) .nil)
  rw [show sint.nat (W64 (0 + 1)) = 1 by rfl] at Hkey
  simp only [List.set_cons_succ, List.set_cons_zero] at Hkey
  have Hkey' := _root_.Perennial.fmt.SprintfOut.str_slash_v_int64 kp x key Hkey
  have Hpk : pfx <+: key := Hk.trans (by rw [Hkey', List.append_assoc]; exact List.prefix_append _ _)
  wp_apply hPNK kv pfx key val (W64 0) lo $$ [$Hpkg $Hkv $Hlo] as %rev %err Hres
  · ipureintro; exact Hpk
  icases Hres with (⟨%Heq, #Hr, #Hc, %Hrr⟩ | ⟨#HerrK, %Hrev, -⟩ | ⟨⟨%Hne, %Hrev⟩, #Hce⟩)
  · -- created
    subst Heq
    wp_auto
    wp_alloc rk as Hrk
    wp_auto
    wp_for_post
    iapply HΦ
    ileft
    isplitr
    · ipureintro; rfl
    iexists key, rev
    unfold ownRemoteKV RemoteKVSt.val'
    iframe Hrk Hr Hc
    ipureintro
    refine ⟨by rw [Hkey']; exact List.prefix_append _ _, Hrr.1, Hrr.2, x, Hkey'⟩
  · -- `ErrKeyExists`: `errors.Is` holds, try again
    unfold concurrency.isPkgErr
    icases HerrK with ⟨#HerrK, %Hne⟩
    icombine HeK HerrK gives %Heq
    subst Heq
    wp_auto
    wp_apply errors.wp_Is_leaf eK (GoInterface.ok eK) HeKl.2.1 HeKl.2.2
      (fun tii h => by cases h; exact HeKl.1) $$ [$Herr]
    (try wp_auto)
    wp_for_post
    simp only [named]
    iframe
  · -- another error: `errors.Is` may say anything
    obtain ⟨e, rfl⟩ : ∃ e, err = GoInterface.ok e := by
      cases err with
      | nil => exact absurd rfl Hne
      | ok e => exact ⟨e, rfl⟩
    iunfold clientErrIs at Hce
    ihave ⟨%S, %M, #Htree, %HS⟩ := Hce $$ %(GoInterface.ok eK)
    wp_auto
    wp_apply errors.wp_Is S M (GoInterface.ok e) (GoInterface.ok eK) $$ [$Herr $Htree] as %b -
    · ipureintro; exact HS.1
    cases b
    · wp_auto
      wp_for_post
      iapply HΦ
      iright
      ipureintro; exact ⟨Hne, rfl⟩
    · wp_auto
      wp_for_post
      simp only [named]
      iframe

end proof

end recipes
end EtcdGrove
end Perennial

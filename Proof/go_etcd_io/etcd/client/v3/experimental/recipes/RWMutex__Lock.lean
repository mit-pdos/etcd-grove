/-
Proof of `Spec/go_etcd_io/etcd/client/v3/experimental/recipes/RWMutex__Lock.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.experimental.recipes.RWMutex__Lock
public import Spec.go_etcd_io.etcd.client.v3.experimental.recipes.RWMutex__waitOnLastRev
public import Spec.go_etcd_io.etcd.client.v3.experimental.recipes.newUniqueEphemeralKey

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

theorem RWMutex.Lock.wp_proof
    (wp_newUniqueEphemeralKey : newUniqueEphemeralKey.spec (GF := GF) (hG := hG))
    (wp_waitOnLastRev : RWMutex.waitOnLastRev.spec (GF := GF) (hG := hG)) :
    RWMutex.Lock.spec (GF := GF) (hG := hG) := by
  intro m s γ client id pfx o lo
  wp_start as ⟨#Hm, Hmk, #Hlo⟩
  ihave #Hm' := Hm
  iunfold isRWMutex at Hm'
  icases Hm' with ⟨#Hms, #Hmctx, #Hmpfx, %Hpfx, #Hsess, #Hcl, #Hclosed⟩
  wp_auto
  wp_apply wp_newUniqueEphemeralKey s γ client id pfx (pfx ++ go!"write") lo
    $$ [$Hsess $Hcl $Hlo] as %ek %err Hres
  · ipureintro; exact List.prefix_append _ _
  icases Hres with (⟨%Hnil, %kv, %key, %r, #HKVf, Hek, #Hr, #Hc, %Hkr⟩ | %Hne)
  rotate_left
  · obtain ⟨Hne, -⟩ := Hne
    obtain ⟨e, rfl⟩ : ∃ e, err = GoInterface.ok e := by
      cases err with
      | nil => exact absurd rfl Hne
      | ok e => exact ⟨e, rfl⟩
    wp_auto
    iapply HΦ
    unfold rwLockResult
    iright
    isplitr
    · ipureintro; exact Hne
    iexists o
    iexact Hmk
  subst Hnil
  ihave #Hc' := Hc
  iunfold keyCreatedAt at Hc'
  icases Hc' with ⟨-, %sc, -, %Hcp⟩
  ihave ⟨%ek0, Hmk⟩ := rwMyKey_field m pfx o $$ Hmk
  wp_auto
  ihave Hmk := rwMyKey_new m client pfx (pfx ++ go!"write") key kv ek r
    (List.prefix_append _ _) Hkr.1 $$ [$Hmk $Hek $HKVf $Hcl]
  ihave IH : iprop("Hmk" ∷ rwMyKey m pfx (some (ek, ⟨GoInterface.ok kv, key, r, []⟩))) $$ [Hmk]
  · simp only [named]; iexact Hmk
  wp_for IH
  wp_apply wp_waitOnLastRev m s γ client id pfx pfx ek _ r $$ [$Hm $Hmk $Hr]
    as %done %werr ⟨Hmk, Hw⟩
  · ipureintro; exact ⟨List.prefix_refl _, Hcp.1⟩
  icases Hw with (⟨%Hd, %R, %s', #HR, #Hs', %HRs⟩ | %Hd)
  · obtain ⟨rfl, rfl⟩ := Hd
    wp_auto
    wp_for_post
    iapply HΦ
    unfold rwLockResult
    ileft
    isplitr
    · ipureintro; rfl
    iexists ek, _, R
    iframe Hmk Hc HR
    isplitr
    · unfold rwHeldAt
      iexists s'
      iframe Hs'
      ipureintro; exact ⟨Hkr.1, Hcp.1, HRs.1, HRs.2⟩
    ipureintro; exact ⟨Hkr.2.1, fun h => by cases h⟩
  subst Hd
  cases werr with
  | ok e =>
    wp_auto
    wp_for_post
    iapply HΦ
    unfold rwLockResult
    iright
    isplitr
    · ipureintro; intro h; cases h
    iexists _
    iexact Hmk
  | nil =>
    wp_auto
    wp_for_post
    iframe

end proof

end recipes
end EtcdGrove
end Perennial

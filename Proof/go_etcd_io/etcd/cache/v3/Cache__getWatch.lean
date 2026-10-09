/-
Proof of `Spec/Cache__getWatch.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.cache.v3.Cache__getWatch
public import Spec.go_etcd_io.etcd.cache.v3.Cache__get
public import Spec.go_etcd_io.etcd.cache.v3.Cache__watch

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.cache.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- The store writer's state satisfies the store's invariant. -/
theorem storeWriter_storeInv (s : Loc) (γ : StoreNames) (cap : Nat) (E : w64 → KvMap → IProp GF)
    (R : w64 → IProp GF) (st : StoreState) :
    storeWriter s γ cap E R st ⊢ storeWriter s γ cap E R st ∗ ⌜StoreInv cap st⌝ := by
  unfold storeWriter
  iintro ⟨H1, H2, H3, H4, H5, %Hi⟩
  iframe
  ipureintro; exact ⟨Hi, Hi⟩

theorem Cache.getWatch.wp_proof
    (wp_get : Cache.get.spec (GF := GF) (hG := hG))
    (wp_watch : Cache.watch.spec (GF := GF) (hG := hG)) :
    Cache.getWatch.spec (GF := GF) (hG := hG) := by
  intro c cf γr γd cap c0 st
  wp_start as ⟨#Hc, Hw, Hwr⟩
  ihave #Hc' := Hc
  iunfold isCacheFields at Hc'
  iNamed Hc'
  icases HisICtx with ⟨%ics, #Hctxi, -⟩
  icases storeWriter_storeInv _ _ _ _ _ _ $$ Hwr with ⟨Hwr, %Hst⟩
  wp_auto
  wp_apply wp_get c cf γr γd cap cf.ictx ics st $$ [$Hpkg $Hc $Hctxi $Hwr] as %resp %err Hres
  icases Hres with (⟨%Herr, Hwr⟩ | ⟨%Herr, %R, %m, #Hrev, Hwr, #HR, -, %HRb⟩)
  · -- the get failed: return its error
    obtain ⟨-, Hne⟩ := Herr
    obtain ⟨e, rfl⟩ : ∃ e, err = GoInterface.ok e := by
      cases err with
      | nil => exact absurd rfl Hne
      | ok e => exact ⟨e, rfl⟩
    wp_auto
    iapply HΦ
    isplitr
    · ipureintro; intro h; cases h
    iexists c0, st
    iframe
  subst Herr
  iunfold getRespRev at Hrev
  icases Hrev with ⟨%hdr, #Hh, %Hnn, #Hr⟩
  wp_auto
  have hR0 : 0 ≤ sint.Z R := by have := Hst.rev_nonneg; omega
  have hR1 : sint.Z (R + W64 1) = sint.Z R + 1 := by
    have := HRb.2; word
  wp_apply wp_watch c cf γr γd cap (R + W64 1) R c0 (restoreState R m) $$ [$Hpkg $Hc $Hw $Hwr]
    as %err ⟨%Hne, %c1, %st', Hw, Hwr⟩
  · isplitl []
    · simp only [restoreState]; iexact HR
    ipureintro
    refine ⟨restoreState_synced R m, by omega, by omega, ?_⟩
    simp only [restoreState]; exact Int.le_refl _
  iapply HΦ
  isplitr
  · ipureintro; exact Hne
  iexists c1, st'
  iframe

end proof

end EtcdGrove
end Perennial

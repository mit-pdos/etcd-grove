/-
Proof of `Spec/validateRevisions.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.cache.v3.validateRevisions
public import Spec.go_etcd_io.etcd.client.v3.WatchResponse__IsProgressNotify

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.cache.v3 go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

theorem validateRevisions.wp_proof
    (wp_IsProgressNotify : WatchResponse.IsProgressNotify.spec (GF := GF) (hG := hG)) :
    validateRevisions.spec (GF := GF) (hG := hG) := by
  intro resp r latestRev
  wp_start as #Hresp
  wp_auto
  wp_apply wp_IsProgressNotify $$ [$resp $Hresp] as resp
  have Hhdr0 : r.isProgressNotify = true → r.hdrRev ≠ W64 0 := by
    intro h hz; simp [RespModel.isProgressNotify, hz] at h
  ihave Hresp2 := Hresp
  simp only [respAt, eventsAt]
  icases Hresp2 with ⟨⟨%ls, #Hsl, %Hlen, #Hall⟩, #Hhdr, %Hf⟩
  cases hp : r.isProgressNotify
  · wp_auto
    ihave %Hsl_len := ownSlice_len _ _ _ $$ Hsl
    wp_if_destruct
    · iapply HΦ
      ipureintro
      have : r.events = [] := by
        rw [← List.length_eq_zero_iff, ← Hlen]; word
      simp [validRevisions, hp, this]
    · iclear Hresp
      ihave HI : iprop(∃ (n : w64) (evp : Loc),
          "i" ∷ i_ptr ↦ n ∗ "ev" ∷ ev_ptr ↦ evp ∗
          "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ sint.Z resp.Events'.len ∧
            ∀ (j : Nat) e, j < sint.nat n → r.events[j]? = some e →
              sint.Z latestRev < sint.Z e.rev⌝) $$ [i ev]
      · iexists W64 0, _
        simp only [named]
        iframe
        ipureintro
        refine ⟨by word, by word, fun j e hj _ => ?_⟩
        exfalso; have : sint.nat (W64 0) = 0 := rfl; omega
      wp_for HI
      wp_if_destruct
      · obtain ⟨evp', Hevp⟩ : ∃ x, ls[sint.nat n]? = some x :=
          ⟨_, List.getElem?_eq_getElem (by word)⟩
        obtain ⟨e, He⟩ : ∃ e, r.events[sint.nat n]? = some e :=
          ⟨_, List.getElem?_eq_getElem (by rw [← Hlen]; word)⟩
        rw [ite_eq_left (by word)]
        wp_apply wp_load_slice_index resp.Events' (sint.Z n) ls DFrac.discard evp' Hn.1 $$ [Hsl] as _
        · iframe Hsl; ipureintro; exact Hevp
        ihave Hev := Hall $$ %(sint.nat n) %evp' %e %Hevp %He
        simp only [eventAt]
        icases Hev with ⟨%keySl, #Htyp, #Hkv, #Hkey, #Hks, #Hmod⟩
        wp_auto
        have Hmem : e ∈ r.events := List.mem_of_getElem? He
        have Hbad : ∀ lr : w64, sint.Z e.rev ≤ sint.Z lr → validRevisions r lr = false := by
          intro lr hlr
          simp only [validRevisions, hp, Bool.false_eq_true, ↓reduceIte, List.all_eq_false]
          exact ⟨e, Hmem, by simp; omega⟩
        wp_if_destruct
        · wp_apply wp_slice_literal
          isplitr
          · ipureintro; rfl
          iintro %sl ⟨Hsl', -⟩
          wp_apply fmt.wp_Errorf $$ [$Hsl'] as %er _
          wp_for_post
          iapply HΦ
          ipureintro
          rw [Hbad _ (by omega)]
          exact ⟨er, rfl⟩
        · wp_if_destruct
          · wp_apply wp_slice_literal
            isplitr
            · ipureintro; rfl
            iintro %sl ⟨Hsl', -⟩
            wp_apply fmt.wp_Errorf $$ [$Hsl'] as %er _
            wp_for_post
            iapply HΦ
            ipureintro
            rw [Hbad _ (by omega)]
            exact ⟨er, rfl⟩
          · wp_for_post
            iframe
            iexists n + W64 1, evp'
            simp only [named]
            iframe
            ipureintro
            refine ⟨by word, by word, fun j e' hj he' => ?_⟩
            rcases Nat.lt_or_ge j (sint.nat n) with h | h
            · exact Hn.2.2 j e' h he'
            · have : j = sint.nat n := by word
              subst this
              rw [He] at he'; cases he'
              have h1 : ¬ sint.Z e.rev < sint.Z latestRev := ‹_›
              have h2 : e.rev ≠ latestRev := ‹_›
              have : sint.Z e.rev ≠ sint.Z latestRev := fun h => h2 (by word)
              omega
      · iapply HΦ
        ipureintro
        have : validRevisions r latestRev = true := by
          simp only [validRevisions, hp, Bool.false_eq_true, ↓reduceIte, List.all_eq_true]
          intro x hx
          obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hx
          have := (List.getElem?_eq_some_iff.1 hj).1
          simp only [decide_eq_true_eq]
          exact Hn.2.2 j x (by rw [← Hlen] at this; word) hj
        rw [this]; simp
  · have Hne := Hhdr0 hp
    simp only [hdrAt]
    icases Hhdr with (%Hnull | ⟨%Hnn, #Hh⟩)
    · exact absurd Hnull.2 Hne
    wp_auto
    wp_if_destruct
    · wp_apply wp_slice_literal
      isplitr
      · ipureintro; rfl
      iintro %sl ⟨Hsl', -⟩
      wp_apply fmt.wp_Errorf $$ [$Hsl'] as %e _
      iapply HΦ
      ipureintro
      simp only [validRevisions, hp, ↓reduceIte]
      simp only [Hif, _root_.decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      exact ⟨e, rfl⟩
    · iapply HΦ
      ipureintro
      simp only [validRevisions, hp, ↓reduceIte]
      simp [Hif]

end proof

end EtcdGrove
end Perennial

/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/linkv3p/clientStep.lean`. Lean-first (no Rocq
counterpart). The range check (a return); the bridge out of the read-only slice and its ownership
out of the `[∗list]`; by the kind, `Blackhole` (only if `holed[a]` is `false`, the flag the
ownership carries: `Blackhole`'s premise) and `holed[a] = true`, or `Unblackhole` and
`holed[a] = false`, or `DropConnections`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.linkv3p.clientStep
public import Spec.github_com.mit_pdos.etcd_grove.third_party.bridge.bridge__Blackhole
public import Spec.github_com.mit_pdos.etcd_grove.third_party.bridge.bridge__Unblackhole
public import Spec.github_com.mit_pdos.etcd_grove.third_party.bridge.bridge__DropConnections

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace linkv3p

open Iris Iris.BI Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.linkv3p.Assumptions]

theorem clientStep.wp_proof
    (wp_Blackhole : bridge.bridge.Blackhole.spec (GF := GF) (hG := hG))
    (wp_Unblackhole : bridge.bridge.Unblackhole.spec (GF := GF) (hG := hG))
    (wp_DropConnections : bridge.bridge.DropConnections.spec (GF := GF) (hG := hG)) :
    clientStep.spec (GF := GF) (hG := hG) := by
  intro brs holed bs hs kind a
  wp_start as ⟨#Hbrs, Hholed, Hown⟩
  ihave #Pbr : isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.third_party.bridge
    $$ []
  · iPkgInit
  ihave %Hbl := ownSlice_len $$ Hbrs
  ihave %Hhl := ownSlice_len $$ Hholed
  ihave %Hlen := BigSepL2.bigSepL2_length $$ Hown
  wp_auto
  wp_if_destruct
  · iapply HΦ; iexists hs; iframe
  have hA0 := Hif
  (try wp_auto)
  wp_if_destruct
  · iapply HΦ; iexists hs; iframe
  have hAn := Hif
  (try wp_auto)
  have hA : 0 ≤ sint.Z a ∧ (sint.Z a).toNat < bs.length := by
    rw [Hbl.1]; unfold sint.nat; constructor <;> word
  have hAb : 0 ≤ sint.Z a ∧ sint.Z a < sint.Z brs.len := by constructor <;> word
  have hAh : 0 ≤ sint.Z a ∧ sint.Z a < sint.Z holed.len := by
    constructor
    · word
    · have : (sint.Z a).toNat < hs.length := by rw [← Hlen]; exact hA.2
      rw [Hhl.1] at this; unfold sint.nat at this; word
  list_elem bs (sint.Z a).toNat as br
  list_elem hs (sint.Z a).toNat as h
  have hbs : bs.set (sint.Z a).toNat br = bs := by
    obtain ⟨hi, hx⟩ := List.getElem?_eq_some_iff.mp Hbr_lookup
    rw [← hx]; exact List.set_getElem_self hi
  have hhs : hs.set (sint.Z a).toNat h = hs := by
    obtain ⟨hi, hx⟩ := List.getElem?_eq_some_iff.mp Hh_lookup
    rw [← hx]; exact List.set_getElem_self hi
  simp only [hAb, _root_.and_self, ↓reduceIte]
  wp_apply wp_load_slice_index _ (sint.Z a) bs _ br hA.1 $$ [] as -
  · iframe #; ipureintro; exact Hbr_lookup
  (try wp_auto)
  icases (BigSepL2.bigSepL2_insert_acc (Φ := fun _ br h =>
    iprop(∃ addr : GoString, bridge.ownBridge (GF := GF) br addr h)) Hbr_lookup Hh_lookup) $$ Hown
    with ⟨⟨%addr, Hob⟩, Hback⟩
  iunfold bridge.ownBridge at Hob
  icases Hob with ⟨%bp, %γ, %Hbrv, #Hb, Hh⟩
  subst Hbrv
  wp_if_destruct
  · -- a blackhole, unless the bridge is blackholed
    simp only [hAh, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index _ (sint.Z a) hs _ h hAh.1 $$ [Hholed] as Hholed
    · iframe; ipureintro; exact Hh_lookup
    (try wp_auto)
    cases h
    · (try wp_auto)
      wp_apply (wp_Blackhole bp γ addr) $$ [Hh] as Hh
      · iframe #; iframe
      (try wp_auto)
      simp only [hAh, _root_.and_self, ↓reduceIte]
      wp_apply wp_store_slice_index _ (sint.Z a) hs true $$ [Hholed] as Hholed
      · iframe; ipureintro; constructor <;> word
      (try wp_auto)
      iapply HΦ
      iexists hs.set (sint.Z a).toNat true
      iframe
      ihave Hall := Hback $$ %(interface.mkOk (go.GoType.PointerType
          github_com.mit_pdos.etcd_grove.third_party.bridge.bridge.ty) #bp) %true
      rw [hbs]
      iapply Hall
      iexists addr
      iunfold bridge.ownBridge
      iexists bp, γ
      iframe #
      iframe
      ipureintro; rfl
    · (try wp_auto)
      iapply HΦ
      iexists hs
      iframe
      ihave Hall := Hback $$ %(interface.mkOk (go.GoType.PointerType
        github_com.mit_pdos.etcd_grove.third_party.bridge.bridge.ty) #bp) %true
      rw [hbs, hhs]
      iapply Hall
      iexists addr
      iunfold bridge.ownBridge
      iexists bp, γ
      iframe #
      iframe
      ipureintro; rfl
  (try wp_auto)
  wp_if_destruct
  · -- an unblackhole
    wp_apply (wp_Unblackhole bp γ addr h) $$ [Hh] as Hh
    · iframe #; iframe
    (try wp_auto)
    simp only [hAh, _root_.and_self, ↓reduceIte]
    wp_apply wp_store_slice_index _ (sint.Z a) hs false $$ [Hholed] as Hholed
    · iframe; ipureintro; constructor <;> word
    (try wp_auto)
    iapply HΦ
    iexists hs.set (sint.Z a).toNat false
    iframe
    ihave Hall := Hback $$ %(interface.mkOk (go.GoType.PointerType
      github_com.mit_pdos.etcd_grove.third_party.bridge.bridge.ty) #bp) %false
    rw [hbs]
    iapply Hall
    iexists addr
    iunfold bridge.ownBridge
    iexists bp, γ
    iframe #
    iframe
    ipureintro; rfl
  · -- a drop
    wp_apply (wp_DropConnections bp γ addr) $$ []
    · iframe #
    (try wp_auto)
    iapply HΦ
    iexists hs
    iframe
    ihave Hall := Hback $$ %(interface.mkOk (go.GoType.PointerType
      github_com.mit_pdos.etcd_grove.third_party.bridge.bridge.ty) #bp) %h
    rw [hbs, hhs]
    iapply Hall
    iexists addr
    iunfold bridge.ownBridge
    iexists bp, γ
    iframe #
    iframe
    ipureintro; rfl

end proof

end linkv3p
end EtcdGrove
end Perennial

/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/etcd/leasecatchup/listed.lean`. Lean-first.

The loop over the listing (as leasegrant's `Main`'s): `found` is whether `id` is among the ids
before the index.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.leasecatchup.listed

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_leasecatchup

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.leasecatchup.Assumptions]

theorem listed.wp_proof : listed.spec (GF := GF) (hG := hG) := by
  intro ls sl ids id
  wp_start as ⟨#Hf, #Hsl⟩
  wp_auto
  ihave %Hlen := ownSlice_len $$ Hsl
  rw [List.length_map] at Hlen
  rename_i gi
  irename : (gi ↦ zero_val w64 : IProp GF) => gi
  ihave IO : (∃ (n gv : w64) (b : Bool), "i" ∷ i_ptr ↦ n ∗ "gi" ∷ gi ↦ gv ∗
      "found" ∷ found_ptr ↦ b ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ (b = true ↔ id ∈ ids.take (sint.nat n))⌝ : IProp GF)
      $$ [i gi found]
  · iexists W64 0, _, false
    simp only [named]
    iframe
    ipureintro
    refine ⟨by decide, ?_⟩
    rw [show sint.nat (W64 0) = 0 by rfl]
    simp
  wp_for IO
  wp_if_destruct
  · -- the `n`th lease
    have Hif' : sint.Z n < sint.Z sl.len := by simpa using Hif
    clear Hif
    have Hlt : sint.nat n < ids.length := by word
    obtain ⟨x, hx⟩ : ∃ x, ids[sint.nat n]? = some x := ⟨_, List.getElem?_eq_getElem Hlt⟩
    have hxs : (ids.map (fun id => (go_etcd_io.etcd.client.v3.LeaseStatus.mk id)))[sint.nat n]? =
        some (go_etcd_io.etcd.client.v3.LeaseStatus.mk x) := by simp [hx]
    have Hbnd : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z sl.len := ⟨Hn.1, Hif'⟩
    simp only [Hbnd, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index _ (sint.Z n) _ DFrac.discard _ Hn.1 $$ [Hsl] as -
    · iframe Hsl; ipureintro; exact hxs
    icases ownSlice_elem_acc (sint.Z n) _ sl DFrac.discard _ Hn.1 hxs $$ Hsl with ⟨#Hxn, -⟩
    icases (go_etcd_io.etcd.client.v3.LeaseStatus.LeaseStatus_access_load_ID
        (sliceIndexRef go_etcd_io.etcd.client.v3.LeaseStatus (sint.Z n) sl)
        (go_etcd_io.etcd.client.v3.LeaseStatus.mk x) DFrac.discard).access_strict $$ Hxn
      with ⟨#Hxid, -⟩
    (try wp_auto)
    (try simp only [Hbnd, _root_.and_self, ↓reduceIte])
    (try wp_auto)
    have hsn : sint.nat (n + W64 1) = sint.nat n + 1 := by word
    have htake : ids.take (sint.nat (n + W64 1)) = ids.take (sint.nat n) ++ [x] := by
      rw [hsn, List.take_add_one, hx]; rfl
    by_cases hxg : x = id
    · rw [decide_eq_true hxg]
      (try wp_auto)
      wp_for_post
      iframe
      iexists n + W64 1, n, true
      simp only [named]
      iframe
      ipureintro
      refine ⟨by word, ?_⟩
      rw [htake]; simp [hxg]
    · rw [decide_eq_false hxg]
      (try wp_auto)
      wp_for_post
      iframe
      iexists n + W64 1, n, b
      simp only [named]
      iframe
      ipureintro
      refine ⟨by word, ?_⟩
      rw [htake, Hn.2]
      simp only [List.mem_append, List.mem_singleton]
      constructor
      · exact Or.inl
      · rintro (h | h)
        · exact h
        · exact absurd h.symm hxg
  · -- the end: `found` is whether `id` is listed
    have hb : b = decide (id ∈ ids) := by
      have h := Hn.2
      rw [List.take_of_length_le (by word)] at h
      cases b <;> simp_all
    subst hb
    (try wp_auto)
    iapply HΦ; itrivial

end proof

end etcd_leasecatchup
end EtcdGrove
end Perennial

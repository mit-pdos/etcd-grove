/-
Proof of `Spec/ringBuffer__findLastIndexLessOrEqual.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.cache.v3.ringBuffer__findLastIndexLessOrEqual
public import Spec.go_etcd_io.etcd.cache.v3.ringBuffer__at

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.cache.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

-- `wp_load` from a fractional struct points-to: a field-store `AccessStrict` instance
-- (which needs `DFrac.own 1`) is found first and the search does not backtrack to the
-- load instance, so the store instances are switched off here (this proof only loads).
attribute [-instance] ringBuffer.ringBuffer_access_store_buffer
  ringBuffer.ringBuffer_access_store_head ringBuffer.ringBuffer_access_store_tail
  ringBuffer.ringBuffer_access_store_size ringBuffer.ringBuffer_access_store_revisionOf

/-- The binary search keeps `left ≤ right + 1` in `[0, n]`, every item before `left`
at most `pivot`, every item after `right` above it. -/
theorem ringBuffer.findLastIndexLessOrEqual.wp_proof
    (wp_at : ringBuffer.«at».spec (GF := GF) (hG := hG)) :
    ringBuffer.findLastIndexLessOrEqual.spec (GF := GF) (hG := hG) := by
  intro T' _ _ T _ V r cap isItem revOf items dq pivot
  wp_start as H
  ihave %Hn := (show ownRingBuffer r cap isItem revOf items dq ⊢ ⌜items.length ≤ cap ∧ cap ≤ 2 ^ 61⌝ from by
    iintro H; iNamed H; ipureintro; exact ⟨Hok.size_le, Hok.cap_le⟩) $$ H
  iNamed H
  wp_auto
  have Hsz := Hok.size
  ihave H := ownRingBuffer_intro r cap isItem revOf items rb ents Hok Hrev Hsorted dq $$ Hr Hbuf Hitems HrevOf
  iclear Hitems HrevOf
  ihave HI : iprop(∃ (lo hi : w64),
      "left" ∷ left_ptr ↦ lo ∗
      "right" ∷ right_ptr ↦ hi ∗
      "H" ∷ ownRingBuffer r cap isItem revOf items dq ∗
      "%Hb" ∷ ⌜0 ≤ sint.Z lo ∧ sint.Z lo ≤ sint.Z hi + 1 ∧ sint.Z hi < items.length⌝ ∗
      "%Hlt" ∷ ⌜∀ j v, j < sint.nat lo → items[j]? = some v → sint.Z (revOf v) ≤ sint.Z pivot⌝ ∗
      "%Hge" ∷ ⌜∀ (j : Nat) v, sint.Z hi < j → items[j]? = some v →
        sint.Z pivot < sint.Z (revOf v)⌝) $$ [left right H]
  · iexists W64 0, rb.size' - W64 1
    simp only [named]
    iframe left right H
    ipureintro
    refine ⟨by word, fun j v hj _ => by word, fun j v hj hv => ?_⟩
    exfalso
    have := (List.getElem?_eq_some_iff.1 hv).1
    word
  wp_for HI
  wp_if_destruct
  · -- the loop body: probe `mid`
    have Hmid := mid_sint lo hi Hb.1 Hif (by omega)
    wp_apply wp_at $$ [$H] as %e %v ⟨H, % ⟨Hv, Herev⟩, -⟩
    · ipureintro; constructor <;> omega
    rw [Herev]
    have Hm1 : sint.Z lo ≤ sint.Z ((lo + hi) >>> W64 1) := by omega
    have Hm2 : sint.Z ((lo + hi) >>> W64 1) ≤ sint.Z hi := by omega
    wp_if_destruct
    · -- `rev(items[mid]) ≤ pivot`: everything up to `mid` is at most `pivot`
      wp_for_post
      iframe
      iexists (lo + hi) >>> W64 1 + W64 1, hi
      simp only [named]
      iframe
      ipureintro
      refine ⟨by word, fun j w hj hw => ?_, Hge⟩
      rcases Nat.lt_or_ge j (sint.nat ((lo + hi) >>> W64 1)) with h | h
      · have := Hsorted.lt hw Hv h; omega
      · have : j = sint.nat ((lo + hi) >>> W64 1) := by word
        subst this; rw [Hv] at hw; cases hw; omega
    · -- `pivot < rev(items[mid])`: everything from `mid` on is above `pivot`
      wp_for_post
      iframe
      iexists lo, (lo + hi) >>> W64 1 - W64 1
      simp only [named]
      iframe
      ipureintro
      refine ⟨by word, Hlt, fun j w hj hw => ?_⟩
      rcases Nat.lt_or_ge (sint.nat ((lo + hi) >>> W64 1)) j with h | h
      · have := Hsorted.lt Hv hw h; omega
      · have : j = sint.nat ((lo + hi) >>> W64 1) := by word
        subst this; rw [Hv] at hw; cases hw; omega
  · -- the loop exit: `left = right + 1`
    have Hk : leCount revOf pivot items = sint.nat lo :=
      leCount_eq_of revOf pivot items _ (by word) Hlt
        (fun j v hj hv => Hge j v (by word) hv)
    rw [Hk, show (W64 ((sint.nat lo : Nat) - 1 : Int)) = hi by word]
    iapply HΦ $$ H

end proof

end EtcdGrove
end Perennial

/- Lean-first (no Rocq counterpart).

`cacheContains(model, bucket, linearized, state)`: a loop over the bucket. Each entry's state is
opened from its invariant (`shared_acc`, with the later credit of a pure step before `Equal`) for
its `Equal` against the candidate, and closed after it.
-/
module

public import Spec.github_com.anishathalye.porcupine.cacheContains
public import Spec.github_com.anishathalye.porcupine.bitset__equal

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace porcupine

open Iris Iris.BI Iris.ProofMode github_com.anishathalye.porcupine

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [NaInvG GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.anishathalye.porcupine.Assumptions]

theorem cacheContains.wp_proof (wp_equal : bitset.equal.spec (GF := GF) (hG := hG)) :
    cacheContains.spec (GF := GF) (hG := hG) := fun σ S m p P bk ces dqb lin ws dq k st t => by
  wp_start as ⟨#Heh, Hbk, #Hces, Hlin, Hst, Htok⟩
  ihave %Hlen := ownSlice_len $$ Hbk
  wp_auto
  ihave HI : (∃ (i : w64) (e : cacheEntry),
      "i" ∷ i_ptr ↦ i ∗ "elem" ∷ elem_ptr ↦ e ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z bk.len⌝ : IProp GF) $$ [i elem]
  · iexists W64 0, _
    iframe
    ipureintro; word
  wp_for HI
  wp_if_destruct
  · have Hb' : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z bk.len := ⟨Hi.1, Hif⟩
    simp only [Hb', _root_.and_self, ↓reduceIte]
    list_elem ces (sint.nat i) as ce
    wp_apply wp_load_slice_index bk (sint.Z i) ces dqb ce Hi.1 $$ [Hbk] as Hbk
    · iframe; ipureintro; exact Hce_lookup
    ihave #Hce := BigSepL.bigSepL_lookup (Φ := fun _ ce => cacheEntryOk S p P ce) Hce_lookup $$ Hces
    unfold cacheEntryOk
    icases Hce with ⟨%ws', %t', %k', #Hws', #Ht', %HP⟩
    wp_method_call
    wp_call
    wp_auto
    wp_apply wp_equal $$ [$Hlin $Hws'] as ⟨Hlin, -⟩
    by_cases hw : ws = ws'
    · simp only [hw, _root_.decide_true]
      wp_auto_lc 1
      unfold isEqHash equalSpec
      icases Heh with ⟨-, #Heq, -⟩
      imod shared_acc S p k' ce.state' t' $$ [$Ht' $Htok $Hlc1] with ⟨Hrep, Hclose⟩
      wp_apply Heq $$ %k %k' %st %ce.state' %t %t' [$Hst $Hrep] as %b ⟨Hst, Hrep, %Hb⟩
      imod Hclose $$ Hrep with Htok
      cases b
      · wp_auto
        wp_for_post
        iframe
        iexists i + W64 1, _
        iframe
        ipureintro; word
      · wp_auto
        wp_for_post
        iapply HΦ
        iframe
        ipureintro; intro _
        rw [Hb rfl]; exact HP
    · simp only [hw, _root_.decide_false]
      wp_auto
      wp_for_post
      iframe
      iexists i + W64 1, _
      iframe
      ipureintro; word
  · iapply HΦ
    iframe
    ipureintro; intro h; cases h

end proof

end porcupine
end EtcdGrove
end Perennial

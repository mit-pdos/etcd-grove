/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/etcd/dist/server/inCluster.lean`. Lean-first (no Rocq
counterpart); etcd-dist N5 (`notes/etcd-dist-plan.md` §19). The range over the initial cluster (read-only) with the
whole context as its invariant (`wp_for`), the counter `j` and the copy `p` existential; `return true` from inside
at the entry `pl[j]` that matched, `false` after.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.server.inCluster

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist
namespace server

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.server.Assumptions]

theorem inCluster.wp_proof : inCluster.spec (GF := GF) (hG := hG) := by
  intro cv pl
  wp_start as #Hcl
  ihave %Hlen := ownSlice_len _ _ _ $$ Hcl
  (try wp_auto)
  ihave HI : (∃ (j : Nat) (pv : github_com.mit_pdos.etcd_grove.examples.etcd.dist.server.Peer),
      "i" ∷ i_ptr ↦ W64 j ∗ "p" ∷ p_ptr ↦ pv ∗ "%Hj" ∷ ⌜j ≤ pl.length⌝ : IProp GF) $$ [i p]
  · iexists 0, _
    iframe
    ipureintro; omega
  wp_for HI
  by_cases hj : j < pl.length
  · have hc : sint.Z (W64 (j : Int)) < sint.Z cv.Cluster'.len := by word
    simp only [decide_eq_true hc, ↓reduceIte]
    (try wp_auto)
    have h0 : 0 ≤ sint.Z (W64 (j : Int)) := by word
    simp only [h0, hc, and_self, ↓reduceIte]
    have hsj : (sint.Z (W64 (j : Int))).toNat = j := by word
    obtain ⟨x, hx⟩ : ∃ x, pl[j]? = some x := ⟨_, List.getElem?_eq_getElem hj⟩
    wp_apply (wp_load_slice_index cv.Cluster' (sint.Z (W64 (j : Int))) pl DFrac.discard x h0) $$ [] as -
    · iframe #; ipureintro; rw [hsj]; exact hx
    (try wp_auto)
    by_cases h1 : x.Name' = cv.Name'
    · rw [decide_eq_true h1]
      (try wp_auto)
      by_cases h2 : x.Addr' = cv.Peer'
      · rw [decide_eq_true h2]
        (try wp_auto)
        wp_for_post
        iapply HΦ
        ipureintro
        intro _
        exact ⟨x, List.mem_of_getElem? hx, h1, h2⟩
      · rw [decide_eq_false h2]
        (try wp_auto)
        wp_for_post
        iframe
        iexists (j + 1), x
        have hw : W64 (j : Int) + W64 1 = W64 ((j + 1 : Nat) : Int) := by word
        rw [hw]
        iframe
        ipureintro; omega
    · rw [decide_eq_false h1]
      (try wp_auto)
      wp_for_post
      iframe
      iexists (j + 1), x
      have hw : W64 (j : Int) + W64 1 = W64 ((j + 1 : Nat) : Int) := by word
      rw [hw]
      iframe
      ipureintro; omega
  · have hc : ¬ sint.Z (W64 (j : Int)) < sint.Z cv.Cluster'.len := by word
    simp only [decide_eq_false hc, Bool.false_eq_true, ↓reduceIte]
    (try wp_auto)
    iapply HΦ
    ipureintro
    intro h; cases h

end proof

end server
end etcd_dist
end EtcdGrove
end Perennial

/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): the proof of `Bag__Equal`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Bag__Equal
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Bag__Count

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Etcdraft

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Assumptions]

theorem Bag.Equal.wp_proof (wp_Count : Bag.Count.spec (GF := GF) (hG := hG)) :
    Bag.Equal.spec (GF := GF) (hG := hG) := by
  intro g b h c
  wp_start as ⟨#Hg, #Hh⟩
  ihave #Hg0 := Hg
  iunfold bagRO at Hg0
  icases Hg0 with ⟨%items, #Hits, #Hib⟩
  ihave #Hh0 := Hh
  iunfold bagRO at Hh0
  icases Hh0 with ⟨%citems, #Hcits, #Hcib⟩
  ihave %Hil := ownSlice_len $$ Hits
  ihave %Hbl := BigSepL2.bigSepL2_length $$ Hib
  ihave %Hcil := ownSlice_len $$ Hcits
  ihave %Hcbl := BigSepL2.bigSepL2_length $$ Hcib
  wp_auto
  wp_if_destruct
  · have hlen : b.length = c.length := by rw [← Hbl, ← Hcbl, Hil.1, Hcil.1, Hif]
    ihave IH : iprop(∃ (n : w64) (itv : G.bagItem),
        "i" ∷ i_ptr ↦ n ∗ "it" ∷ it_ptr ↦ itv ∗
        "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ sint.Z g.items'.len ∧
          (b.take (sint.nat n)).all (fun it => c.count it.1 == it.2) = true⌝) $$ [i it]
    · iexists _, _
      iframe
      ipureintro
      refine ⟨by word, by word, by rw [show sint.nat (W64 0) = 0 from rfl]; simp⟩
    wp_for IH
    obtain ⟨hn0, hn1, hna⟩ := Hn
    wp_if_destruct
    · have Hlt : sint.nat n < items.length := by rw [Hil.1]; word
      obtain ⟨y, Hy⟩ : ∃ y, items[sint.nat n]? = some y := ⟨_, List.getElem?_eq_getElem Hlt⟩
      obtain ⟨x, Hx⟩ : ∃ x, b[sint.nat n]? = some x := ⟨_, List.getElem?_eq_getElem (Hbl ▸ Hlt)⟩
      ihave ⟨#Hyx, %Hyc⟩ := BigSepL2.bigSepL2_lookup
        (Φ := fun _ it p => iprop(msgRO (GF := GF) it.msg' p.1 ∗ ⌜sint.Z it.count' = (p.2 : Int)⌝)) Hy Hx $$ Hib
      rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z n ∧ sint.Z n < sint.Z g.items'.len from ⟨hn0, Hif⟩))]
      wp_apply wp_load_slice_index _ (sint.Z n) items DFrac.discard y hn0 $$ [Hits] as -
      · isplitr
        · iexact Hits
        ipureintro; exact Hy
      try wp_auto
      rw [github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Bag.TypeAssumptions.ptr_Count_unfold.method_unfold]
      try wp_auto
      wp_apply wp_Count h c y.msg' x.1 $$ [Hh Hyx] as %cc %Hcc
      · iframe Hh Hyx
      try wp_auto
      have htake : (b.take (sint.nat (n + W64 1))).all (fun it => c.count it.1 == it.2) =
          ((b.take (sint.nat n)).all (fun it => c.count it.1 == it.2) && (c.count x.1 == x.2)) := by
        rw [show sint.nat (n + W64 1) = sint.nat n + 1 by word, List.take_add_one, Hx]
        simp
      have hiff : cc = y.count' ↔ c.count x.1 = x.2 := by
        constructor
        · intro e; have := Hcc; rw [e, Hyc] at this; exact_mod_cast this.symm
        · intro e; have : sint.Z cc = sint.Z y.count' := by rw [Hcc, Hyc, e]
          word
      by_cases hc : cc = y.count'
      · rw [decide_eq_true hc]
        simp only [Bool.not_true]
        try wp_auto
        wp_for_post
        iframe
        iexists _, _
        iframe
        ipureintro
        refine ⟨by word, by word, ?_⟩
        rw [htake, hna, Bool.true_and]
        simpa using hiff.1 hc
      · rw [decide_eq_false hc]
        simp only [Bool.not_false]
        try wp_auto
        wp_for_post
        try wp_auto
        have : b.eq c = false := by
          unfold Bag.eq
          rw [List.all_eq_false.2 ⟨x, List.mem_of_getElem? Hx, by simpa using fun e => hc (hiff.2 e)⟩]
          simp
        rw [this]
        iapply HΦ; ipureintro; trivial
    · try wp_auto
      have hnx : sint.nat n = b.length := by rw [← Hbl, Hil.1]; word
      rw [hnx, List.take_length] at hna
      have : b.eq c = true := by
        unfold Bag.eq; rw [hna]; simp [hlen]
      rw [this]
      iapply HΦ; ipureintro; trivial
  · try wp_auto
    have : b.eq c = false := by
      unfold Bag.eq
      have : b.length ≠ c.length := fun e => Hif (by
        have : sint.nat g.items'.len = sint.nat h.items'.len := by rw [← Hil.1, ← Hcil.1, Hbl, Hcbl, e]
        word)
      simp [this]
    rw [this]
    iapply HΦ; ipureintro; trivial

end proof

end Etcdraft
end EtcdGrove
end Perennial

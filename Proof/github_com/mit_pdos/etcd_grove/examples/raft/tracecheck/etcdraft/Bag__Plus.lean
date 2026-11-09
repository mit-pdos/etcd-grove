/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): the proof of `Bag__Plus`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Bag__Plus
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Bag__add

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Etcdraft

open Iris Iris.BI Iris.ProofMode

section pure

/-- `Bag.add` keeps the messages distinct. -/
theorem Bag.add_nodup (b : Bag) (m : Msg) (n : Nat) (hnd : (b.map Prod.fst).Nodup) :
    ((b.add m n).map Prod.fst).Nodup := by
  unfold Bag.add
  split
  · have : (b.map (fun it => if it.1 == m then (it.1, it.2 + n) else it)).map Prod.fst = b.map Prod.fst := by
      rw [List.map_map]; apply List.map_congr_left; intro it _; simp only [Function.comp_apply]; split <;> rfl
    rw [this]; exact hnd
  · rename_i h
    rw [List.map_append, List.nodup_append]
    refine ⟨hnd, by simp, ?_⟩
    intro a ha b' hb' hab
    simp only [List.map_cons, List.map_nil, List.mem_singleton] at hb'
    subst hb'; subst hab
    apply h
    obtain ⟨it, hit, e⟩ := List.mem_map.1 ha
    exact List.any_eq_true.2 ⟨it, hit, by simp [e]⟩

theorem Bag.map_upd_sum (b : Bag) (m : Msg) (n : Nat) (hnd : (b.map Prod.fst).Nodup)
    (h : b.any (fun it => it.1 == m) = true) :
    ((b.map (fun it => if it.1 == m then (it.1, it.2 + n) else it)).map Prod.snd).sum =
      (b.map Prod.snd).sum + n := by
  induction b with
  | nil => simp at h
  | cons x xs ih =>
    rw [List.map_cons, List.nodup_cons] at hnd
    by_cases hx : (x.1 == m) = true
    · have hxs : ∀ y ∈ xs, (y.1 == m) = false := by
        intro y hy
        rw [beq_eq_false_iff_ne]
        intro e
        apply hnd.1
        rw [List.mem_map]
        exact ⟨y, hy, by rw [e]; exact (beq_iff_eq.1 hx).symm⟩
      have hmap : xs.map (fun it => if it.1 == m then (it.1, it.2 + n) else it) = xs := by
        conv => rhs; rw [← List.map_id xs]
        apply List.map_congr_left
        intro y hy
        rw [hxs y hy]; rfl
      simp only [List.map_cons, hx, ite_true, hmap, List.sum_cons]
      omega
    · rw [Bool.not_eq_true] at hx
      have h' : xs.any (fun it => it.1 == m) = true := by simpa [hx] using h
      simp only [List.map_cons, hx, Bool.false_eq_true, ite_false, List.sum_cons]
      rw [ih hnd.2 h']
      omega

/-- `Bag.add` adds `n` to the total count (the messages distinct). -/
theorem Bag.add_sum (b : Bag) (m : Msg) (n : Nat) (hnd : (b.map Prod.fst).Nodup) :
    ((b.add m n).map Prod.snd).sum = (b.map Prod.snd).sum + n := by
  unfold Bag.add
  split
  · rename_i h
    exact Bag.map_upd_sum b m n hnd h
  · simp

theorem nat_le_sum_of_mem {l : List Nat} {a : Nat} (h : a ∈ l) : a ≤ l.sum := by
  induction l with
  | nil => simp at h
  | cons x xs ih =>
    rw [List.sum_cons]
    rcases List.mem_cons.1 h with rfl | h
    · exact Nat.le_add_right _ _
    · exact Nat.le_trans (ih h) (Nat.le_add_left _ _)

/-- A count is at most the total. -/
theorem Bag.count_le_sum (b : Bag) (m : Msg) : b.count m ≤ (b.map Prod.snd).sum := by
  unfold Bag.count
  split
  · rename_i it hit
    exact nat_le_sum_of_mem (List.mem_map.2 ⟨it, List.mem_of_find?_eq_some hit, rfl⟩)
  · exact Nat.zero_le _

/-- The counts of a prefix and the next item are at most the total. -/
theorem Bag.sum_take_succ_le (c : Bag) (j : Nat) (x : Msg × Nat) (hx : c[j]? = some x) :
    ((c.take j).map Prod.snd).sum + x.2 ≤ (c.map Prod.snd).sum := by
  have e : ((c.take (j + 1)).map Prod.snd).sum = ((c.take j).map Prod.snd).sum + x.2 := by
    rw [List.take_add_one, hx]; simp
  rw [← e]
  conv => rhs; rw [← List.take_append_drop (j + 1) c]
  rw [List.map_append, List.sum_append]
  exact Nat.le_add_right _ _

end pure

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Assumptions]

theorem Bag.Plus.wp_proof (wp_add : Bag.add.spec (GF := GF) (hG := hG)) :
    Bag.Plus.spec (GF := GF) (hG := hG) := by
  intro g b h c
  wp_start as ⟨#Hg, #Hh, %Hnd, %Hsum⟩
  ihave #Hh0 := Hh
  iunfold bagRO at Hh0
  icases Hh0 with ⟨%citems, #Hcits, #Hcib⟩
  ihave %Hcil := ownSlice_len $$ Hcits
  ihave %Hcbl := BigSepL2.bigSepL2_length $$ Hcib
  wp_auto
  ihave IH : iprop(∃ (j : w64) (itv : G.bagItem) (outv : G.Bag),
      "i" ∷ i_ptr ↦ j ∗ "it" ∷ it_ptr ↦ itv ∗ "out" ∷ out_ptr ↦ outv ∗
      "Hacc" ∷ bagRO outv ((c.take (sint.nat j)).foldl (fun acc it => acc.add it.1 it.2) b) ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z h.items'.len ∧
        List.Nodup (((c.take (sint.nat j)).foldl (fun acc it => acc.add it.1 it.2) b).map Prod.fst) ∧
          (((c.take (sint.nat j)).foldl (fun acc it => acc.add it.1 it.2) b).map Prod.snd).sum = (b.map Prod.snd).sum + ((c.take (sint.nat j)).map Prod.snd).sum⌝) $$ [i it out]
  · iexists _, _, _
    iframe
    rw [show sint.nat (W64 0) = 0 from rfl, List.take_zero, List.foldl_nil]
    isplitr
    · iexact Hg
    ipureintro
    refine ⟨by word, by word, Hnd, by simp⟩
  wp_for IH
  obtain ⟨hn0, hn1, hacc⟩ := Hn
  wp_if_destruct
  · have Hlt : sint.nat j < citems.length := by rw [Hcil.1]; word
    obtain ⟨y, Hy⟩ : ∃ y, citems[sint.nat j]? = some y := ⟨_, List.getElem?_eq_getElem Hlt⟩
    obtain ⟨x, Hx⟩ : ∃ x, c[sint.nat j]? = some x := ⟨_, List.getElem?_eq_getElem (Hcbl ▸ Hlt)⟩
    ihave ⟨#Hyx, %Hyc⟩ := BigSepL2.bigSepL2_lookup
      (Φ := fun _ it p => iprop(msgRO (GF := GF) it.msg' p.1 ∗ ⌜sint.Z it.count' = (p.2 : Int)⌝)) Hy Hx $$ Hcib
    rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z j ∧ sint.Z j < sint.Z h.items'.len from ⟨hn0, Hif⟩))]
    wp_apply wp_load_slice_index _ (sint.Z j) citems DFrac.discard y hn0 $$ [Hcits] as -
    · isplitr
      · iexact Hcits
      ipureintro; exact Hy
    try wp_auto
    rw [github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Bag.TypeAssumptions.ptr_add_unfold.method_unfold]
    try wp_auto
    have htake : (c.take (sint.nat (j + W64 1))).foldl (fun acc it => acc.add it.1 it.2) b =
        ((c.take (sint.nat j)).foldl (fun acc it => acc.add it.1 it.2) b).add x.1 x.2 := by
      rw [show sint.nat (j + W64 1) = sint.nat j + 1 by word, List.take_add_one, Hx]
      simp
    wp_apply wp_add _ _ y.msg' x.1 y.count' x.2 $$ [Hacc Hyx] as %g' Hg'
    · iframe Hacc Hyx
      ipureintro
      refine ⟨hacc.1, Hyc, ?_⟩
      have h1 := Bag.count_le_sum (List.foldl (fun acc it => acc.add it.1 it.2) b (List.take (sint.nat j) c)) x.1
      have h2 := Bag.sum_take_succ_le c (sint.nat j) x Hx
      rw [hacc.2] at h1
      omega
    try wp_auto
    wp_for_post
    iframe
    iexists _, _, _
    iframe
    rw [htake]
    iframe Hg'
    ipureintro
    refine ⟨by word, by word, ?_⟩
    refine ⟨Bag.add_nodup _ _ _ hacc.1, ?_⟩
    rw [Bag.add_sum _ _ _ hacc.1, hacc.2, show sint.nat (j + W64 1) = sint.nat j + 1 by word,
      List.take_add_one, Hx]
    simp only [Option.toList_some, List.map_append, List.sum_append, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil]
    omega
  · try wp_auto
    have hjx : sint.nat j = c.length := by rw [← Hcbl, Hcil.1]; word
    rw [hjx, List.take_length]
    iapply HΦ
    unfold Bag.plus
    iexact Hacc

end proof

end Etcdraft
end EtcdGrove
end Perennial

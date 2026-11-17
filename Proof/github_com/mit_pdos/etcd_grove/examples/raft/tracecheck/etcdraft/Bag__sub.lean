/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): the proof of `Bag__sub`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Bag__sub
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Bag__find

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Etcdraft

open Iris Iris.BI Iris.ProofMode

section pure

/-- `Bag.sub`, `m` not in the bag: the bag itself. -/
theorem Bag.sub_notfound (b : Bag) (m : Msg) (n : Nat)
    (hf : b.findIdx? (fun it => it.1 == m) = none) : b.sub m n = b := by
  unfold Bag.sub
  rw [List.findIdx?_eq_none_iff] at hf
  induction b with
  | nil => rfl
  | cons x xs ih =>
    rw [List.filterMap_cons, show (x.1 == m) = false from hf x List.mem_cons_self]
    simp only [Bool.false_eq_true, ite_false]
    rw [ih (fun y hy => hf y (List.mem_cons_of_mem _ hy))]

/-- In a bag with distinct messages, the item at `j` holds `m` exactly at `m`'s position. -/
theorem Bag.match_iff (b : Bag) (m : Msg) (i j : Nat) (x : Msg × Nat) (hnd : (b.map Prod.fst).Nodup)
    (hf : b.findIdx? (fun it => it.1 == m) = some i) (hx : b[j]? = some x) :
    (x.1 == m) = decide (j = i) := by
  obtain ⟨hil, him, -⟩ := List.findIdx?_eq_some_iff_getElem.1 hf
  have hjl : j < b.length := (List.getElem?_eq_some_iff.1 hx).1
  have hxj : b[j] = x := (List.getElem?_eq_some_iff.1 hx).2
  by_cases hji : j = i
  · subst hji; rw [decide_eq_true rfl, ← hxj]; exact him
  · rw [decide_eq_false hji]
    have : x.1 ≠ m := by
      intro hxm
      have e1 : (b.map Prod.fst)[j]'(by simpa using hjl) = (b.map Prod.fst)[i]'(by simpa using hil) := by
        simp only [List.getElem_map]; rw [hxj, hxm]; exact (beq_iff_eq.1 him).symm
      exact hji (hnd.eq_of_getElem_eq _ _ e1)
    simpa using this

/-- `Bag.sub`'s step on one item. -/
def Bag.subF (m : Msg) (n : Nat) (it : Msg × Nat) : Option (Msg × Nat) :=
  if it.1 == m then (if it.2 > n then some (it.1, it.2 - n) else none) else some it

theorem Bag.sub_eq (b : Bag) (m : Msg) (n : Nat) : b.sub m n = b.filterMap (Bag.subF m n) := rfl

end pure

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Assumptions]

theorem Bag.sub.wp_proof (wp_find : Bag.find.spec (GF := GF) (hG := hG)) :
    Bag.sub.spec (GF := GF) (hG := hG) := by
  intro g b p m nw n
  wp_start as ⟨#Hg, #Hm, %Hnd, %Hn⟩
  ihave #Hg0 := Hg
  iunfold bagRO at Hg0
  icases Hg0 with ⟨%items, #Hits, #Hib⟩
  ihave %Hil := ownSlice_len $$ Hits
  ihave %Hbl := BigSepL2.bigSepL2_length $$ Hib
  iapply wp_fupd
  wp_auto
  rw [github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Bag.TypeAssumptions.ptr_find_unfold.method_unfold]
  try wp_auto
  wp_apply wp_find g b p m $$ [Hg Hm] as %k %Hk
  · iframe Hg Hm
  try wp_auto
  cases hf : b.findIdx? (fun it => it.1 == m) with
  | none =>
    rw [hf] at Hk
    simp only at Hk
    rw [decide_eq_true (show sint.Z k < sint.Z (W64 0) by rw [Hk]; decide)]
    try wp_auto
    iapply HΦ
    rw [Bag.sub_notfound b m n hf]
    iexact Hg
  | some i =>
    rw [hf] at Hk
    simp only at Hk
    have hk0 : 0 ≤ sint.Z k := by rw [Hk]; exact Int.natCast_nonneg _
    rw [decide_eq_false (show ¬ sint.Z k < sint.Z (W64 0) by rw [show sint.Z (W64 0) = 0 from rfl]; omega)]
    try wp_auto
    ihave #Hnil := ownSlice_nil (V := G.bagItem) (GF := GF) (DFrac.own 1)
    ihave Hcap0 := ownSliceCap_nil (V := G.bagItem) (GF := GF)
    ihave IH : iprop(∃ (h : w64) (itv : G.bagItem) (hv : w64) (osl : GoSlice) (L : List G.bagItem),
        "i" ∷ i_ptr ↦ h ∗ "it" ∷ it_ptr ↦ itv ∗ "h" ∷ h_ptr ↦ hv ∗ "items" ∷ items_ptr ↦ osl ∗
        "Hout" ∷ osl ↦* L ∗ "Hcap" ∷ ownSliceCap G.bagItem osl (DFrac.own 1) ∗
        "Hrel" ∷ ([∗list] it;q ∈ L;(b.take (sint.nat h)).filterMap (Bag.subF m n),
          msgRO (GF := GF) it.msg' q.1 ∗ ⌜sint.Z it.count' = (q.2 : Int)⌝) ∗
        "%Hn" ∷ ⌜0 ≤ sint.Z h ∧ sint.Z h ≤ sint.Z g.items'.len⌝) $$ [i it h items Hcap0]
    · iexists _, _, _, slice.nil, []
      iframe
      isplitr
      · iexact Hnil
      isplitr
      · iexact Hcap0
      rw [show sint.nat (W64 0) = 0 from rfl, List.take_zero, List.filterMap_nil]
      isplitr
      · iapply BigSepL2.bigSepL2_nil.2; iempintro
      ipureintro; exact ⟨by word, by word⟩
    wp_for IH
    obtain ⟨hn0, hn1⟩ := Hn
    wp_if_destruct
    · have Hlt : sint.nat h < items.length := by rw [Hil.1]; word
      obtain ⟨y, Hy⟩ : ∃ y, items[sint.nat h]? = some y := ⟨_, List.getElem?_eq_getElem Hlt⟩
      obtain ⟨x, Hx⟩ : ∃ x, b[sint.nat h]? = some x := ⟨_, List.getElem?_eq_getElem (Hbl ▸ Hlt)⟩
      ihave ⟨#Hyx, %Hyc⟩ := BigSepL2.bigSepL2_lookup
        (Φ := fun _ it p => iprop(msgRO (GF := GF) it.msg' p.1 ∗ ⌜sint.Z it.count' = (p.2 : Int)⌝)) Hy Hx $$ Hib
      rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z h ∧ sint.Z h < sint.Z g.items'.len from ⟨hn0, Hif⟩))]
      wp_apply wp_load_slice_index _ (sint.Z h) items DFrac.discard y hn0 $$ [Hits] as -
      · isplitr
        · iexact Hits
        ipureintro; exact Hy
      try wp_auto
      have htake : (b.take (sint.nat (h + W64 1))).filterMap (Bag.subF m n) =
          (b.take (sint.nat h)).filterMap (Bag.subF m n) ++ (Bag.subF m n x).toList := by
        rw [show sint.nat (h + W64 1) = sint.nat h + 1 by word, List.take_add_one, Hx]
        simp only [Option.toList_some, List.filterMap_append, List.filterMap_cons, List.filterMap_nil]
        cases Bag.subF m n x <;> rfl
      have hmatch := Bag.match_iff b m i (sint.nat h) x Hnd hf Hx
      have hki : (h = k) ↔ sint.nat h = i := by
        constructor
        · intro e; rw [e]; have : sint.Z k = (i : Int) := Hk; word
        · intro e; have : sint.Z k = (i : Int) := Hk; word
      by_cases hhk : h = k
      · rw [decide_eq_true hhk]
        simp only [Bool.not_true]
        try wp_auto
        have hxm : (x.1 == m) = true := by rw [hmatch]; exact decide_eq_true (hki.1 hhk)
        by_cases hc : n < x.2
        · have hz : sint.Z nw < sint.Z y.count' := by rw [Hn, Hyc]; exact_mod_cast hc
          rw [decide_eq_true hz]
          try wp_auto
          wp_apply wp_slice_literal
          isplitr
          · ipureintro; rfl
          iintro %sl0 ⟨Hsl0, -⟩
          wp_apply wp_slice_append $$ [Hout Hcap Hsl0] as %s2 ⟨Hs2, Hcap2, -⟩
          · iframe
          try wp_auto
          wp_for_post
          iframe
          iexists _, _, _, _, _
          iframe
          isplitl [Hrel]
          · rw [htake, show Bag.subF m n x = some (x.1, x.2 - n) by simp [Bag.subF, hxm, hc]]
            simp only [Option.toList_some]
            iapply (BigSepL2.bigSepL2_snoc).2
            iframe Hrel Hyx
            ipureintro
            have h0 : 0 ≤ sint.Z nw := by rw [Hn]; exact Int.natCast_nonneg _
            rw [show sint.Z (y.count' - nw) = sint.Z y.count' - sint.Z nw by word, Hyc, Hn]
            simp only; push_cast [Nat.le_of_lt hc]; rfl
          ipureintro; exact ⟨by word, by word⟩
        · have hz : ¬ sint.Z nw < sint.Z y.count' := by rw [Hn, Hyc]; exact_mod_cast hc
          rw [decide_eq_false hz]
          try wp_auto
          wp_for_post
          iframe
          iexists _, _, _, _, _
          iframe
          isplitl [Hrel]
          · rw [htake, show Bag.subF m n x = none by simp [Bag.subF, hxm, hc]]
            simp only [Option.toList_none, List.append_nil]
            iexact Hrel
          ipureintro; exact ⟨by word, by word⟩
      · rw [decide_eq_false hhk]
        simp only [Bool.not_false]
        try wp_auto
        have hxm : (x.1 == m) = false := by rw [hmatch]; exact decide_eq_false (fun e => hhk (hki.2 e))
        wp_apply wp_slice_literal
        isplitr
        · ipureintro; rfl
        iintro %sl0 ⟨Hsl0, -⟩
        wp_apply wp_slice_append $$ [Hout Hcap Hsl0] as %s2 ⟨Hs2, Hcap2, -⟩
        · iframe
        try wp_auto
        wp_for_post
        iframe
        iexists _, _, _, _, _
        iframe
        isplitl [Hrel]
        · rw [htake, show Bag.subF m n x = some x by simp [Bag.subF, hxm]]
          simp only [Option.toList_some]
          iapply (BigSepL2.bigSepL2_snoc).2
          iframe Hrel Hyx
          ipureintro; exact Hyc
        ipureintro; exact ⟨by word, by word⟩
    · have hhx : sint.nat h = b.length := by rw [← Hbl, Hil.1]; word
      rw [hhx, List.take_length] at *
      try wp_auto
      imod ownSlice_persist $$ Hout with #Hout
      imodintro
      iapply HΦ
      rw [Bag.sub_eq]
      iunfold bagRO
      iexists _
      iframe Hout
      iexact Hrel

end proof

end Etcdraft
end EtcdGrove
end Perennial

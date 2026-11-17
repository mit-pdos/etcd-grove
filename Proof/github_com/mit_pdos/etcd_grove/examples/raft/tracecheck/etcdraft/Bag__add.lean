/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): the proof of `Bag__add`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Bag__add
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Bag__find

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Etcdraft

open Iris Iris.BI Iris.ProofMode

section pure

/-- `Bag.add` on a bag whose messages are distinct, `m` found at `k`: item `k` updated. -/
theorem Bag.add_found (b : Bag) (m : Msg) (n k : Nat) (x : Msg × Nat) (hnd : (b.map Prod.fst).Nodup)
    (hf : b.findIdx? (fun it => it.1 == m) = some k) (hx : b[k]? = some x) :
    b.add m n = b.set k (x.1, x.2 + n) := by
  have hk := (List.findIdx?_eq_some_iff_getElem.1 hf)
  obtain ⟨hkl, hkm, -⟩ := hk
  have hxk : b[k] = x := by rw [List.getElem?_eq_some_iff] at hx; exact hx.2
  have hxm : x.1 = m := by rw [← hxk]; simpa using hkm
  unfold Bag.add
  rw [ite_eq_left (List.any_eq_true.2 ⟨x, List.mem_of_getElem? hx, by simp [hxm]⟩)]
  apply List.ext_getElem?
  intro j
  rw [List.getElem?_map, List.getElem?_set]
  by_cases hj : k = j
  · subst hj; rw [ite_eq_left rfl, hx]; simp [hxm, hkl]
  · rw [ite_eq_right hj]
    cases hbj : b[j]? with
    | none => rfl
    | some y =>
      have hyx : y.1 ≠ m := by
        intro hym
        have hjl : j < b.length := (List.getElem?_eq_some_iff.1 hbj).1
        have e1 : (b.map Prod.fst)[j]'(by simpa using hjl) = (b.map Prod.fst)[k]'(by simpa using hkl) := by
          simp only [List.getElem_map]
          rw [(List.getElem?_eq_some_iff.1 hbj).2, hxk, hym, hxm]
        exact hj (hnd.eq_of_getElem_eq _ _ e1).symm
      simp [hyx]

/-- `Bag.add`, `m` not in the bag: appended. -/
theorem Bag.add_notfound (b : Bag) (m : Msg) (n : Nat)
    (hf : b.findIdx? (fun it => it.1 == m) = none) : b.add m n = b ++ [(m, n)] := by
  unfold Bag.add
  have : b.any (fun it => it.1 == m) = false := by
    rw [← List.findIdx?_isSome, hf]; rfl
  rw [this]; rfl

/-- `Bag.count` at the found position. -/
theorem Bag.count_found (b : Bag) (m : Msg) (k : Nat) (x : Msg × Nat)
    (hf : b.findIdx? (fun it => it.1 == m) = some k) (hx : b[k]? = some x) : b.count m = x.2 := by
  unfold Bag.count; rw [List.find?_eq_bind_findIdx?_getElem?, hf]; simp [hx]

end pure

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Assumptions]

theorem Bag.add.wp_proof (wp_find : Bag.find.spec (GF := GF) (hG := hG)) :
    Bag.add.spec (GF := GF) (hG := hG) := by
  intro g b p m nw n
  wp_start as ⟨#Hg, #Hm, %Hnd, %Hn, %Hbound⟩
  ihave #Hg0 := Hg
  iunfold bagRO at Hg0
  icases Hg0 with ⟨%items, #Hits, #Hib⟩
  ihave %Hil := ownSlice_len $$ Hits
  ihave %Hbl := BigSepL2.bigSepL2_length $$ Hib
  iapply wp_fupd
  wp_auto
  ihave #Hnil := ownSlice_nil (V := G.bagItem) (GF := GF) (DFrac.own 1)
  ihave Hcap0 := ownSliceCap_nil (V := G.bagItem) (GF := GF)
  wp_apply wp_slice_append slice.nil [] g.items' items DFrac.discard $$ [Hnil Hcap0 Hits] as %s1 ⟨Hs1, Hcap1, -⟩
  · iframe Hnil Hcap0 Hits
  try wp_auto
  rw [github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Bag.TypeAssumptions.ptr_find_unfold.method_unfold]
  try wp_auto
  wp_apply wp_find g b p m $$ [Hg Hm] as %k %Hk
  · iframe Hg Hm
  try wp_auto
  rw [List.nil_append]
  ihave %Hs1l := ownSlice_len $$ Hs1
  cases hf : b.findIdx? (fun it => it.1 == m) with
  | none =>
    rw [hf] at Hk
    simp only at Hk
    rw [decide_eq_false (show ¬ sint.Z (W64 0) ≤ sint.Z k by rw [Hk]; decide)]
    try wp_auto
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %sl0 ⟨Hsl0, -⟩
    wp_apply wp_slice_append $$ [Hs1 Hcap1 Hsl0] as %s2 ⟨Hs2, -, -⟩
    · iframe
    try wp_auto
    imod ownSlice_persist $$ Hs2 with #Hs2
    imodintro
    iapply HΦ
    rw [Bag.add_notfound b m n hf]
    iunfold bagRO
    iexists _
    iframe Hs2
    iapply (BigSepL2.bigSepL2_snoc).2
    iframe Hib
    iframe Hm
    ipureintro; exact Hn
  | some i =>
    rw [hf] at Hk
    simp only at Hk
    have hi : i < b.length := ((List.findIdx?_eq_some_iff_getElem).1 hf).1
    obtain ⟨x, Hx⟩ : ∃ x, b[i]? = some x := ⟨_, List.getElem?_eq_getElem hi⟩
    obtain ⟨y, Hy⟩ : ∃ y, items[i]? = some y := ⟨_, List.getElem?_eq_getElem (Hbl ▸ hi)⟩
    have hk0 : 0 ≤ sint.Z k := by rw [Hk]; exact Int.natCast_nonneg _
    rw [decide_eq_true (show sint.Z (W64 0) ≤ sint.Z k from hk0)]
    try wp_auto
    have hkl : sint.Z k < sint.Z s1.len := by
      have : (i : Int) < items.length := by rw [Hbl]; exact_mod_cast hi
      rw [Hs1l.1] at this; rw [Hk]; word
    have hki : (sint.Z k).toNat = i := by rw [Hk]; simp
    rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z k ∧ sint.Z k < sint.Z s1.len from ⟨hk0, hkl⟩))]
    icases ownSlice_elem_acc _ y _ _ items hk0 (by rw [hki]; exact Hy) $$ Hs1 with ⟨Hy', Hback⟩
    try wp_auto
    rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z k ∧ sint.Z k < sint.Z s1.len from ⟨hk0, hkl⟩))]
    try wp_auto
    rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z k ∧ sint.Z k < sint.Z s1.len from ⟨hk0, hkl⟩))]
    try wp_auto
    ihave Hs := Hback $$ Hy'
    rw [hki]
    imod ownSlice_persist $$ Hs with #Hs
    imodintro
    iapply HΦ
    rw [Bag.add_found b m n i x Hnd hf Hx]
    icases BigSepL2.bigSepL2_insert_acc
      (Φ := fun _ it p => iprop(msgRO (GF := GF) it.msg' p.1 ∗ ⌜sint.Z it.count' = (p.2 : Int)⌝)) Hy Hx $$ Hib
      with ⟨⟨#Hyx, %Hyc⟩, Hset⟩
    have hcx : b.count m = x.2 := Bag.count_found b m i x hf Hx
    iunfold bagRO
    iexists _
    iframe Hs
    iapply Hset
    iframe Hyx
    ipureintro
    simp only
    have : sint.Z y.count' + sint.Z nw < 2 ^ 63 := by rw [Hyc, Hn, ← hcx]; exact Hbound
    have h0 : 0 ≤ sint.Z y.count' := by rw [Hyc]; exact Int.natCast_nonneg _
    have h1 : 0 ≤ sint.Z nw := by rw [Hn]; exact Int.natCast_nonneg _
    rw [show sint.Z (y.count' + nw) = sint.Z y.count' + sint.Z nw by word, Hyc, Hn]
    push_cast; rfl

end proof

end Etcdraft
end EtcdGrove
end Perennial

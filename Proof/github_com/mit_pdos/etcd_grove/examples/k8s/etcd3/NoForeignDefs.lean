/-
Lean-first (no Rocq counterpart).

# The vocabulary of `Seeded.NoForeign`'s spec (k8s-dist K9, `notes/k8s-dist-k9.md` §2.8)

- `nfWriteRV f p`: the revision a successful write of `p` answers with, when above `f` (Go's test in
  `NoForeign`'s loop: `isWrite(in) && out.Err == ENone && out.RV > s.st0.rv`);
- `NoForeignOk f xs m`: what `NoForeign` returning true says, `m` the greatest such revision (or `f`):
  the revisions of those writes are exactly `f+1, ..., m`, and every revision any operation shows is at
  most `m` (`AnchorsOk` with the anchors `0, ..., m`);
- `anchorsOk_mono`, `count_cover`: the two pure steps of its proof (anchors widen; a duplicate-free
  list of `m - f` revisions in `(f, m]` names every one).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.HistRevsDefs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Input Output Obj)

section pure
variable [GooseExts]

/-- The revision a successful write of `p` answers with, when above `f` (see the file header). -/
def nfWriteRV (f : w64) (p : Input × Output) : Option w64 :=
  if isWriteL p.1 = true ∧ p.2.Err' = W64 0 ∧ uint.nat f < uint.nat p.2.RV' then some p.2.RV'
  else none

/-- **What `NoForeign` returning true says** (see the file header). -/
def NoForeignOk (f : w64) (xs : List (Input × Output)) (m : w64) : Prop :=
  (∀ v : w64, (uint.nat f < uint.nat v ∧ uint.nat v ≤ uint.nat m) ↔ ∃ p ∈ xs, nfWriteRV f p = some v) ∧
  k8s_dist.AnchorsOk (List.range (uint.nat m + 1)) xs

theorem opAnchors_mono {A B : List Nat} {x : Input} {y : Output} (h : k8s_dist.OpAnchors A x y)
    (hAB : ∀ a ∈ A, a ∈ B) : k8s_dist.OpAnchors B x y := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨fun r hr => hAB _ (h1 r hr), fun r a b => hAB _ (h2 r a b),
    fun a b evs c e he d => hAB _ (h3 a b evs c e he d), fun hk => ?_⟩
  obtain ⟨g1, g2, g3, g4, g5⟩ := h4 hk
  exact ⟨hAB _ g1, hAB _ g2, fun a => hAB _ (g3 a), fun a b os c o ho => hAB _ (g4 a b os c o ho),
    fun o a b => hAB _ (g5 o a b)⟩

theorem anchorsOk_mono {A B : List Nat} {xs : List (Input × Output)} (h : k8s_dist.AnchorsOk A xs)
    (hAB : ∀ a ∈ A, a ∈ B) : k8s_dist.AnchorsOk B xs :=
  ⟨hAB _ h.1, fun p hp => opAnchors_mono (h.2 p hp) hAB⟩

/-- Every element of a list sorted by `<` is at most its last. -/
theorem le_getLast_of_sorted {l : List w64} (hs : l.Pairwise fun a b => uint.nat a < uint.nat b)
    (hne : l ≠ []) : ∀ a ∈ l, uint.nat a ≤ uint.nat (l.getLast hne) := by
  intro a ha
  have he := List.dropLast_concat_getLast hne
  rw [← he] at hs ha
  rcases List.mem_append.1 ha with h | h
  · exact Nat.le_of_lt (List.pairwise_append.1 hs |>.2.2 a h _ (List.mem_singleton_self _))
  · rw [List.mem_singleton.1 h]; exact Nat.le_refl _

/-- **Counting covers**: a duplicate-free list of `m - f` revisions in `(f, m]` names every one. -/
theorem count_cover (L : List w64) (f m : w64) (hnd : L.Nodup)
    (hin : ∀ k ∈ L, uint.nat f < uint.nat k ∧ uint.nat k ≤ uint.nat m)
    (hlen : L.length = uint.nat m - uint.nat f) (v : w64)
    (hv : uint.nat f < uint.nat v ∧ uint.nat v ≤ uint.nat m) : v ∈ L := by
  have hnd' : (L.map uint.nat).Nodup :=
    List.Pairwise.map uint.nat (fun a b h e => h (by word)) hnd
  have hsub : L.map uint.nat ⊆ List.range' (uint.nat f + 1) (uint.nat m - uint.nat f) := by
    intro k hk
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hk
    have := hin a ha
    rw [List.mem_range']; refine ⟨uint.nat a - (uint.nat f + 1), by omega, by omega⟩
  have hp := (List.subperm_of_subset hnd' hsub).perm_of_length_le (by simp [hlen])
  have : uint.nat v ∈ L.map uint.nat := by
    refine hp.symm.subset ?_
    rw [List.mem_range']; exact ⟨uint.nat v - (uint.nat f + 1), by omega, by omega⟩
  obtain ⟨a, ha, he⟩ := List.mem_map.1 this
  rwa [show v = a by word]

theorem nf_forall₂_getElem {α β : Type} {R : α → β → Prop} :
    ∀ {l1 : List α} {l2 : List β}, List.Forall₂ R l1 l2 →
      ∀ i (h1 : i < l1.length) (h2 : i < l2.length), R l1[i] l2[i]
  | _, _, .cons h _, 0, _, _ => h
  | _, _, .cons _ t, i + 1, h1, h2 =>
    nf_forall₂_getElem t i (by simpa using h1) (by simpa using h2)

/-- `NoForeign`'s loop invariant after the operations `t`: the map `W` holds the revisions of `t`'s
successful writes above `f`, and `m` is the greatest (or `f`). -/
def NfInv (f : w64) (t : List (Input × Output)) (W : GMap w64 Bool) (m : w64) : Prop :=
  (∀ v, (W !! v).isSome ↔ ∃ p ∈ t, nfWriteRV f p = some v) ∧
  uint.nat f ≤ uint.nat m ∧
  (∀ p ∈ t, ∀ v, nfWriteRV f p = some v → uint.nat v ≤ uint.nat m)

theorem nfInv_nil (f : w64) : NfInv f [] ∅ f :=
  ⟨fun v => by simp, Nat.le_refl _, fun p hp => by simp at hp⟩

theorem nfInv_none {f : w64} {t : List (Input × Output)} {W : GMap w64 Bool} {m : w64}
    {p : Input × Output} (h : NfInv f t W m) (hp : nfWriteRV f p = none) : NfInv f (t ++ [p]) W m := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun v => ?_, h2, fun q hq v hv => ?_⟩
  · rw [h1 v]
    constructor
    · rintro ⟨q, hq, e⟩; exact ⟨q, List.mem_append_left _ hq, e⟩
    · rintro ⟨q, hq, e⟩
      rcases List.mem_append.1 hq with hq | hq
      · exact ⟨q, hq, e⟩
      · rw [List.mem_singleton.1 hq, hp] at e; cases e
  · rcases List.mem_append.1 hq with hq | hq
    · exact h3 q hq v hv
    · rw [List.mem_singleton.1 hq, hp] at hv; cases hv

theorem nfInv_some {f : w64} {t : List (Input × Output)} {W : GMap w64 Bool} {m : w64}
    {p : Input × Output} {r : w64} (h : NfInv f t W m) (hp : nfWriteRV f p = some r) :
    NfInv f (t ++ [p]) (<[r := true]> W) (if uint.Z r < uint.Z m then m else r) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hm : uint.nat m ≤ uint.nat (if uint.Z r < uint.Z m then m else r) ∧
      uint.nat r ≤ uint.nat (if uint.Z r < uint.Z m then m else r) := by
    split <;> constructor <;> word
  refine ⟨fun v => ?_, Nat.le_trans h2 hm.1, fun q hq v hv => ?_⟩
  · rw [GMap.lookup_insert_is_Some]
    constructor
    · rintro (rfl | ⟨_, hv⟩)
      · exact ⟨p, List.mem_append_right _ (List.mem_singleton_self _), hp⟩
      · obtain ⟨q, hq, e⟩ := (h1 v).1 hv; exact ⟨q, List.mem_append_left _ hq, e⟩
    · rintro ⟨q, hq, e⟩
      by_cases hrv : r = v
      · exact Or.inl hrv
      · refine Or.inr ⟨hrv, (h1 v).2 ?_⟩
        rcases List.mem_append.1 hq with hq | hq
        · exact ⟨q, hq, e⟩
        · rw [List.mem_singleton.1 hq, hp] at e; cases e; exact absurd rfl hrv
  · rcases List.mem_append.1 hq with hq | hq
    · exact Nat.le_trans (h3 q hq v hv) hm.1
    · rw [List.mem_singleton.1 hq, hp] at hv; cases hv; exact hm.2

theorem nfWriteRV_gt {f : w64} {p : Input × Output} {v : w64} (h : nfWriteRV f p = some v) :
    uint.nat f < uint.nat v := by
  unfold nfWriteRV at h
  split at h
  · cases h; rename_i hc; exact hc.2.2
  · cases h

/-- **The loop's end**: the counting test and the anchors' test give `NoForeignOk`. -/
theorem noForeignOk_of {f : w64} {xs : List (Input × Output)} {W : GMap w64 Bool} {m : w64}
    {A : List w64} (h : NfInv f xs W m) (hsz : GMap.size W = uint.nat m - uint.nat f)
    (hA : k8s_dist.AnchorsOk (0 :: A.map uint.nat) xs) (hAm : ∀ a ∈ A, uint.nat a ≤ uint.nat m) :
    NoForeignOk f xs m := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun v => ⟨fun hv => ?_, fun ⟨p, hp, e⟩ => ⟨nfWriteRV_gt e, h3 p hp v e⟩⟩, ?_⟩
  · refine (h1 v).1 ((GMap.mem_dom_list W v).1 ?_)
    refine count_cover W.domList f m (GMap.nodup_dom_list W) (fun k hk => ?_)
      (by rw [← GMap.size_eq_dom_list_length]; exact hsz) v hv
    obtain ⟨p, hp, e⟩ := (h1 k).1 ((GMap.mem_dom_list W k).1 hk)
    exact ⟨nfWriteRV_gt e, h3 p hp k e⟩
  · refine anchorsOk_mono hA (fun a ha => ?_)
    rw [List.mem_range]
    rcases List.mem_cons.1 ha with rfl | ha
    · omega
    · obtain ⟨b, hb, rfl⟩ := List.mem_map.1 ha; have := hAm b hb; omega

end pure

end k8s_etcd3
end EtcdGrove
end Perennial

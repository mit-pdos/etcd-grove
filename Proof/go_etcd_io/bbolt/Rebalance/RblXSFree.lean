/-
`node.free`'s premises from `rblX` (U8b, `Rebalance/RblXSteps.lean`): a node of a bucket has its
page in the view (`treeWF`, `nodeClean`), its slots covered by the logical tree (`RblXSPos`) so
not pending (`flView`), not free and allocated before the view (`mvccView`), and the freelist's
ids are distinct below `2^62`, so few enough (`rblX_canFree'`).
-/
module

public import Proof.go_etcd_io.bbolt.Rebalance.RblXSPos

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt


open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section free
variable [GooseExts]

/-- Distinct ids below `2^62` are at most `2^62`. -/
theorem nodup_len_le (l : List w64) (hnd : l.Nodup) (hb : ∀ x ∈ l, x.toNat < 2 ^ 62) :
    l.length ≤ 2 ^ 62 := by
  have hnd' : (l.map BitVec.toNat).Nodup :=
    List.pairwise_map.2 (hnd.imp fun h e => h (BitVec.eq_of_toNat_eq e))
  have hsub : l.map BitVec.toNat ⊆ List.range (2 ^ 62) := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    exact List.mem_range.2 (hb y hy)
  have := hnd'.length_le_of_subset hsub
  simpa using this

omit [GooseExts] in
theorem W64_ofInt_toNat (x : w64) : W64 (x.toNat : Int) = x := by simp [W64]

/-- **A node's page and `node.free`'s premises.** -/
theorem rblX_canFree' (X : WX) (fl : FLPg) (bl : Loc) (dfc : Option Loc) (B : BRec) (n : Loc)
    (r : NRec) (hI : rblX X fl bl dfc) (hb : X.t.bs !! bl = some B) (hr : B.ns !! n = some r)
    (hp0 : r.nv.pgid' ≠ W64 0) :
    ∃ pg, X.v.pages !! r.nv.pgid'.toNat = some pg ∧ 16 ≤ pg.length ∧
      pageId pg = r.nv.pgid'.toNat ∧
      (pageFlags pg = branchPageFlag ∨ pageFlags pg = leafPageFlag) ∧
      fl.canFree X.t.mv.txid' r.nv.pgid' (1 + pageOverflow pg) := by
  obtain ⟨⟨-, -, -, htx, -⟩, hBk, -, -, -, -, -, hLR, hFV, -, hext, -⟩ := hI
  obtain ⟨hrb, -, -, hrt, hlive⟩ := hBk bl B hb
  obtain ⟨hc, ⟨bnd, hk⟩, -, -⟩ := hrb
  have hn := hc.2.2.2.2.2.2.2.1 n r hr
  have h0 : B.ib.root' ≠ W64 0 := fun h => hp0 (hn.2.2.2.2.2.2.2.2.1 h)
  have htwf := hn.2.2.2.2.2.2.2.2.2.1 h0
  obtain ⟨rt, hrtI, hd⟩ := hLR.2 bl B n r hb hr (hlive n r hr)
  have hpos := node_pos X bl B hb hc hk.2.1 hrt h0 rt n hrtI hd r hr
  cases htwf with
  | page _ pg h2 hlt hpg hid hlen hpt =>
  refine ⟨pg, hpg, ?_, hid, ?_, ?_⟩
  · rw [hlen]; have := Nat.zero_le (pageOverflow pg); omega
  · cases hpt with
    | leaf _ _ hf _ _ => exact Or.inr hf
    | branch _ _ hf _ _ => exact Or.inl hf
  have hext' : r.nv.pgid'.toNat + (1 + pageOverflow pg) < 2 ^ 64 := by
    have := hext _ pg hpg; omega
  have hov : pageOverflow pg < 2 ^ 32 := by unfold pageOverflow; exact BitVec.isLt _
  have hext0 := posExtent_node X bl B hb hc h0 n r hr hp0 pg hpg
  obtain ⟨hcov, hmv, hnd, hlt62⟩ := hFV
  refine ⟨h2, hext', ?_, ?_, ?_⟩
  · intro x hx hxa
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hx
    have hj' := List.mem_range.1 hj
    have hxn : (r.nv.pgid' + W64 (j : Int)).toNat = r.nv.pgid'.toNat + j := by
      rw [BitVec.toNat_add]
      have : (W64 (j : Int)).toNat = j := by
        simp only [W64, BitVec.toNat_ofInt]; omega
      rw [this]; omega
    obtain ⟨s, hs⟩ : ∃ s, s = r.nv.pgid'.toNat + j := ⟨_, rfl⟩
    have hcs : coversSlot X.v.pages s := ⟨_, pg, hpg, by omega, by omega⟩
    have hlc : lCovers X s := Or.inl ⟨bl, (r.nv.pgid', 1 + pageOverflow pg), by rw [hb]; simp,
      List.mem_filterMap.2 ⟨_, hpos, hext0⟩, by simp only; omega, by simp only; omega⟩
    have hnp := (hcov s hcs).1 hlc
    have hnf := (hmv.2 s hcs).2.1
    have hxe : r.nv.pgid' + W64 (j : Int) = W64 (s : Int) := by
      apply BitVec.eq_of_toNat_eq
      rw [hxn]; simp only [W64, BitVec.toNat_ofInt]; omega
    rcases List.mem_append.1 hxa with h | h
    · rw [hxe] at h; exact hnf h
    · exact hnp (by rw [hs, ← hxn]; exact List.mem_map_of_mem h)
  · cases ha : fl.allocs !! r.nv.pgid' with
    | none =>
      simp only [Option.getD_none]
      intro he
      have : X.t.mv.txid'.toNat = 0 := by rw [← he]; rfl
      omega
    | some a =>
      simp only [Option.getD_some]
      have := hmv.1 _ pg hpg a (by rw [W64_ofInt_toNat]; exact ha)
      intro he; rw [he] at this; omega
  · have := nodup_len_le _ hnd hlt62
    omega

end free

end bbolt
end EtcdGrove
end Perennial

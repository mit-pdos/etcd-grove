/-
`node.spill` after its children's loop (U9z2, `notes/bbolt-proof-plan.md`; pure): **the parent's
put of a piece** (`parPut`): `put(oldKey, …)` of piece `i` into the parent's entries
`parWs bs j i ps` replaces entry `j` (the first piece, at the node's old key) or inserts the
piece's entry after the done pieces', keeping the entries sorted.
-/
module

public import Proof.go_etcd_io.bbolt.Spill.NodeSpillTailInv
public import Proof.go_etcd_io.bbolt.Spill.UTreeFrame
public import Proof.go_etcd_io.bbolt.Write.NodeEnts

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

namespace Spill

section par
variable [GooseExts]

/-- The key of entry `t` of entries given by their data. -/
def dKey (L : List (w32 × w64 × List w8 × List w8)) (t : Nat) : List w8 :=
  ((L[t]?).map fun d => d.2.2.1).getD []

theorem wKey_dKey (ws : List WEntry) (t : Nat) : wKey ws t = dKey (ws.map wDat) t := by
  unfold wKey dKey; rw [List.getElem?_map]; cases ws[t]? <;> rfl

theorem dKey_append_left (A B : List (w32 × w64 × List w8 × List w8)) {t : Nat}
    (h : t < A.length) : dKey (A ++ B) t = dKey A t := by
  unfold dKey; rw [List.getElem?_append_left h]

theorem dKey_append_right (A B : List (w32 × w64 × List w8 × List w8)) {t : Nat}
    (h : A.length ≤ t) : dKey (A ++ B) t = dKey B (t - A.length) := by
  unfold dKey; rw [List.getElem?_append_right h]

theorem wKey_splice (ws : List WEntry) (m d : Nat) (e : WEntry) (hm : m ≤ ws.length) (t : Nat) :
    wKey (ws.take m ++ [e] ++ ws.drop (m + d)) t =
      if t < m then wKey ws t else if t = m then e.key else wKey ws (t - 1 + d) := by
  have hl : (ws.take m).length = m := by simp; omega
  unfold wKey
  rw [List.append_assoc]
  by_cases h1 : t < m
  · rw [if_pos h1, List.getElem?_append_left (by rw [hl]; exact h1), List.getElem?_take_of_lt h1]
  · rw [if_neg h1]
    by_cases h2 : t = m
    · subst h2; rw [if_pos rfl, List.getElem?_append_right (by rw [hl]; exact Nat.le_refl _), hl]; simp
    · rw [if_neg h2, List.getElem?_append_right (by rw [hl]; omega), hl, List.singleton_append,
        List.getElem?_cons, if_neg (by omega), List.getElem?_drop]
      congr 3; omega

/-- **Splicing an entry into sorted entries** (in place of `d` of them) keeps them sorted when its
key is above the keys before and below the keys after. -/
theorem wsSorted_splice (ws : List WEntry) (m d : Nat) (e : WEntry) (hs : wsSorted ws)
    (hm : m + d ≤ ws.length) (h1 : ∀ t < m, go.GoStringLt (wKey ws t) e.key)
    (h2 : ∀ t, m + d ≤ t → t < ws.length → go.GoStringLt e.key (wKey ws t)) :
    wsSorted (ws.take m ++ [e] ++ ws.drop (m + d)) := by
  have hlen : (ws.take m ++ [e] ++ ws.drop (m + d)).length = ws.length + 1 - d := by
    simp; omega
  intro a b hab hb
  rw [hlen] at hb
  rw [wKey_splice ws m d e (by omega), wKey_splice ws m d e (by omega)]
  by_cases ha1 : a < m
  · rw [if_pos ha1]
    by_cases hb1 : b < m
    · rw [if_pos hb1]; exact hs a b hab (by omega)
    · rw [if_neg hb1]
      by_cases hb2 : b = m
      · rw [if_pos hb2]; exact h1 a ha1
      · rw [if_neg hb2]; exact go.goStringLt_trans (h1 a ha1) (h2 _ (by omega) (by omega))
  · rw [if_neg ha1]
    have hb1 : ¬ b < m := by omega
    rw [if_neg hb1]
    by_cases ha2 : a = m
    · rw [if_pos ha2, if_neg (by omega)]; exact h2 _ (by omega) (by omega)
    · rw [if_neg ha2, if_neg (by omega)]; exact hs _ _ (by omega) (by omega)

theorem sorted_le {ws : List WEntry} (hs : wsSorted ws) {a b : Nat} (hab : a ≤ b)
    (hb : b < ws.length) {k : List w8} (h : go.GoStringLt (wKey ws b) k) :
    go.GoStringLt (wKey ws a) k := by
  rcases Nat.lt_or_eq_of_le hab with h' | rfl
  · exact go.goStringLt_trans (hs a b h' hb) h
  · exact h

theorem sorted_ge {ws : List WEntry} (hs : wsSorted ws) {a b : Nat} (hab : a ≤ b)
    (hb : b < ws.length) {k : List w8} (h : go.GoStringLt k (wKey ws a)) :
    go.GoStringLt k (wKey ws b) := by
  rcases Nat.lt_or_eq_of_le hab with h' | rfl
  · exact go.goStringLt_trans h (hs a b h' hb)
  · exact h

/-- **The parent's put of piece `i`** (`e` its entry, data `pcDat pn`, put under `k`): the first
piece's at the node's key `k` (entry `j`) replaces it, a later one's (at its own first key) is
inserted after the done pieces'; the entries stay sorted. -/
theorem parPut {ws bs : List WEntry} {j i : Nat} {ps : List Piece} {k : List w8} {e : WEntry}
    {pn : Piece} (hws : ws.map wDat = parWs bs j i ps) (hs : wsSorted ws) (hlen : ps.length = i)
    (hj : j < bs.length ∨ (bs = [] ∧ j = 0)) (he : wDat e = pcDat pn)
    (h0 : i = 0 → bs ≠ [] → wKey bs j = k) (hk : i ≠ 0 → k = pn.k)
    (hlo : i = 0 → 0 < j → go.GoStringLt (wKey bs (j - 1)) pn.k)
    (hlo' : i ≠ 0 → ∀ p, ps[i - 1]? = some p → go.GoStringLt p.k pn.k)
    (hhi : j + 1 < bs.length → go.GoStringLt pn.k (wKey bs (j + 1))) :
    wsSorted (wsPutAt ws k e) ∧ (wsPutAt ws k e).map wDat = parWs bs j (i + 1) (ps ++ [pn]) := by
  have hek : e.key = pn.k := congrArg (fun d => d.2.2.1) he
  have hjl : j ≤ bs.length := by rcases hj with h | ⟨-, rfl⟩ <;> omega
  have hpar1 : parWs bs j (i + 1) (ps ++ [pn]) =
      (bs.take j).map wDat ++ ps.map pcDat ++ [pcDat pn] ++ (bs.drop (j + 1)).map wDat := by
    unfold parWs; rw [if_neg (Nat.succ_ne_zero _)]; simp
  rw [hpar1]
  by_cases hi : i = 0
  · subst hi
    have hps : ps = [] := List.eq_nil_of_length_eq_zero hlen
    subst hps
    unfold parWs at hws; rw [if_pos rfl] at hws
    have hK : wKey ws = wKey bs := wKey_of_dat hws
    have hL : ws.length = bs.length := length_of_dat hws
    by_cases hb : bs = []
    · subst hb
      have hw0 : ws = [] := by simpa using hws
      subst hw0
      refine ⟨?_, ?_⟩
      · unfold wsPutAt wsIdx; intro a b hab hb'; simp at hb'; omega
      · unfold wsPutAt wsIdx wsFound; simp [he]
    · have hjb : j < bs.length := by rcases hj with h | ⟨h, -⟩; exact h; exact absurd h hb
      obtain ⟨w, hw⟩ : ∃ w, ws[j]? = some w := ⟨_, List.getElem?_eq_getElem (by omega)⟩
      have hwk : w.key = k := by
        rw [← h0 rfl hb, ← hK]; unfold wKey; rw [hw]; rfl
      have hidx : wsIdx ws k = j := by
        have hkj : wKey ws j = k := by unfold wKey; rw [hw]; simp [hwk]
        apply Write.wsIdx_of_bounds ws k j (by omega)
        · intro t ht; rw [← hkj]; exact hs t j ht (by omega)
        · intro _; rw [hkj]; exact go.goStringLt_irrefl _
      have hfd : wsFound ws k := by unfold wsFound; rw [hidx, hw]; simp [hwk]
      have hput : wsPutAt ws k e = ws.take j ++ [e] ++ ws.drop (j + 1) := by
        unfold wsPutAt; rw [if_pos hfd, hidx]
      rw [hput]
      refine ⟨wsSorted_splice ws j 1 e hs (by omega) (fun t ht => ?_) (fun t ht htl => ?_), ?_⟩
      · rw [hek, hK]
        have := hlo rfl (by omega)
        exact sorted_le (wsSorted_of_dat hws.symm hs) (by omega) (by omega) this
      · rw [hek, hK]
        exact sorted_ge (wsSorted_of_dat hws.symm hs) (by omega) (by omega) (hhi (by omega))
      · simp only [List.map_append, List.map_take, List.map_drop, hws, List.map_cons,
          List.map_nil, he, List.map_nil, List.append_nil]
  · have hm : j + i ≤ ws.length := by
      have := congrArg List.length hws
      unfold parWs at this; rw [if_neg hi] at this
      simp at this; omega
    have hTJ : ((bs.take j).map wDat).length = j := by simp; omega
    have hPS : (ps.map pcDat).length = i := by simp [hlen]
    unfold parWs at hws; rw [if_neg hi] at hws
    -- the keys around the insertion point
    have hkm1 : wKey ws (j + i - 1) = ((ps[i - 1]?).map Piece.k).getD [] := by
      rw [wKey_dKey, hws, dKey_append_left _ _ (by rw [List.length_append]; omega),
        dKey_append_right _ _ (by omega), hTJ]
      unfold dKey; rw [List.getElem?_map, show j + i - 1 - j = i - 1 by omega]
      cases ps[i - 1]? <;> rfl
    have hkm : j + i < ws.length → wKey ws (j + i) = wKey bs (j + 1) := by
      intro hlt
      rw [wKey_dKey, hws, dKey_append_right _ _ (by rw [List.length_append]; omega),
        List.length_append, hTJ, hPS, show j + i - (j + i) = 0 by omega, wKey_dKey]
      unfold dKey; rw [List.map_drop, List.getElem?_drop]
    have hwl : ws.length = j + i + (bs.length - (j + 1)) := by
      have := congrArg List.length hws; simp at this; omega
    obtain ⟨p, hp⟩ : ∃ p, ps[i - 1]? = some p := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    have hlast : go.GoStringLt (wKey ws (j + i - 1)) pn.k := by
      rw [hkm1, hp]; exact hlo' hi p hp
    have hup : j + i < ws.length → go.GoStringLt pn.k (wKey ws (j + i)) := fun hlt => by
      rw [hkm hlt]; exact hhi (by omega)
    rw [hk hi]
    have hidx : wsIdx ws pn.k = j + i := Write.wsIdx_of_bounds ws pn.k (j + i) hm
      (fun t ht => sorted_le hs (by omega) (by omega) hlast)
      (fun hlt => go.goStringLt_asymm (hup hlt))
    have hnf : ¬ wsFound ws pn.k := by
      rw [Write.wsFound_iff, hidx]
      rintro ⟨hlt, he'⟩
      have := hup hlt; rw [he'] at this; exact go.goStringLt_irrefl _ this
    have hput : wsPutAt ws pn.k e = ws.take (j + i) ++ [e] ++ ws.drop (j + i + 0) := by
      unfold wsPutAt; rw [if_neg hnf, hidx]; rfl
    rw [hput]
    refine ⟨wsSorted_splice ws (j + i) 0 e hs (by omega) (fun t ht => ?_) (fun t ht htl => ?_), ?_⟩
    · rw [hek]; exact sorted_le hs (by omega) (by omega) hlast
    · rw [hek]; exact sorted_ge hs (by omega) htl (hup (by omega))
    · rw [Nat.add_zero, List.map_append, List.map_append, List.map_take, List.map_drop, hws]
      rw [List.take_append_of_le_length (by rw [List.length_append]; omega),
        List.take_of_length_le (by rw [List.length_append]; omega),
        List.drop_append_of_le_length (by rw [List.length_append]; omega),
        List.drop_of_length_le (by rw [List.length_append]; omega)]
      simp [he]

end par

end Spill

end bbolt
end EtcdGrove
end Perennial

/-
The spill's pure tree facts (U9f, `notes/bbolt-proof-plan.md`): **the parent's branch after a
child's spill** (`uBr_replace`): entry `j`'s unspilled child replaced by the pieces, finished
subtrees (`node.spill`'s children's loop).
-/
module

public import Proof.go_etcd_io.bbolt.Spill.UTreeParent

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove
namespace bbolt

open go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

namespace Spill

section esp
variable {α β : Type} {es L : List α} {j : Nat}

theorem esp_lt (hj : j < es.length) {i : Nat} (hi : i < j) :
    (es.take j ++ L ++ es.drop (j + 1))[i]? = es[i]? := by
  rw [List.append_assoc, List.getElem?_append_left (by simp; omega), List.getElem?_take_of_lt hi]

theorem esp_mid (hj : j < es.length) {k : Nat} (hk : k < L.length) :
    (es.take j ++ L ++ es.drop (j + 1))[j + k]? = L[k]? := by
  rw [List.append_assoc, List.getElem?_append_right (by simp; omega),
    List.getElem?_append_left (by simp; omega)]
  simp only [List.length_take]
  rw [show j + k - min j es.length = k by omega]

theorem esp_hi (hj : j < es.length) {k : Nat} (hjk : j < k) (hL : 0 < L.length) :
    (es.take j ++ L ++ es.drop (j + 1))[k + L.length - 1]? = es[k]? := by
  rw [List.append_assoc, List.getElem?_append_right (by simp; omega),
    List.getElem?_append_right (by simp; omega)]
  simp only [List.length_take]
  rw [show k + L.length - 1 - min j es.length - L.length = k - (j + 1) by omega,
    List.getElem?_drop, show j + 1 + (k - (j + 1)) = k by omega]

theorem esp_length (hj : j < es.length) :
    (es.take j ++ L ++ es.drop (j + 1)).length = es.length + L.length - 1 := by
  simp; omega

theorem esp_split (hj : j < es.length) : es = es.take j ++ es[j] :: es.drop (j + 1) := by
  conv => lhs; rw [← List.take_append_drop j es]
  rw [List.drop_eq_getElem_cons hj]

theorem esp_flatMap_sub (f : α → List β) (hj : j < es.length) (hL : L.flatMap f = []) :
    ((es.take j ++ L ++ es.drop (j + 1)).flatMap f).Sublist (es.flatMap f) := by
  conv => rhs; rw [esp_split (es := es) hj]
  simp only [List.flatMap_append, hL, List.append_nil, List.flatMap_cons]
  exact List.Sublist.append (List.Sublist.refl _) (List.sublist_append_right _ _)

theorem esp_filterMap_sub (f : α → Option β) (hj : j < es.length) (hL : L.filterMap f = []) :
    ((es.take j ++ L ++ es.drop (j + 1)).filterMap f).Sublist (es.filterMap f) := by
  conv => rhs; rw [esp_split (es := es) hj]
  simp only [List.filterMap_append, hL, List.append_nil]
  apply List.Sublist.append (List.Sublist.refl _)
  rw [List.filterMap_cons]
  split
  · exact List.Sublist.refl _
  · exact List.sublist_cons_self _ _

theorem flatMap_disj {f : α → List β} (hnd : (es.flatMap f).Nodup) {a b : Nat} {ea eb : α}
    (ha : es[a]? = some ea) (hb : es[b]? = some eb) (hab : a ≠ b) {x : β} (hx : x ∈ f ea) :
    x ∉ f eb := by
  have hpw := List.pairwise_iff_getElem.1 (List.pairwise_flatMap.1 hnd).2
  obtain ⟨ha', rfl⟩ := List.getElem?_eq_some_iff.1 ha
  obtain ⟨hb', rfl⟩ := List.getElem?_eq_some_iff.1 hb
  intro hy
  rcases Nat.lt_or_gt_of_ne hab with h | h
  · exact hpw a b ha' hb' h x hx x hy rfl
  · exact hpw b a hb' ha' h x hy x hx rfl

end esp

section keys
variable [GooseExts]
variable {ws ws' : List WEntry} {ps : List Piece} {j : Nat}

theorem splice_key_lt
    (hd : ws'.map wDat = (ws.take j).map wDat ++ ps.map pcDat ++ (ws.drop (j + 1)).map wDat)
    (hj : j < ws.length) {i : Nat} (hi : i < j) : wKey ws' i = wKey ws i := by
  obtain ⟨w', w, h1, h2, hw⟩ := splice_lt hd hj hi
  rw [wKey_of_get h1, wKey_of_get h2, wDat_key hw]

theorem splice_key_mid
    (hd : ws'.map wDat = (ws.take j).map wDat ++ ps.map pcDat ++ (ws.drop (j + 1)).map wDat)
    (hj : j < ws.length) {k : Nat} (hk : k < ps.length) : wKey ws' (j + k) = pcKey ps k := by
  obtain ⟨w', x, h1, h2, hw⟩ := splice_mid hd hj hk
  rw [wKey_of_get h1, pcKey_of_get h2]
  exact congrArg (fun d => d.2.2.1) hw

theorem splice_key_hi
    (hd : ws'.map wDat = (ws.take j).map wDat ++ ps.map pcDat ++ (ws.drop (j + 1)).map wDat)
    (hj : j < ws.length) {k : Nat} (hjk : j < k) (hk : k < ws.length) :
    wKey ws' (k + ps.length - 1) = wKey ws k := by
  obtain ⟨w', w, h1, h2, hw⟩ := splice_hi hd hj hjk hk
  rw [wKey_of_get h1, wKey_of_get h2, wDat_key hw]

/-- **The spliced entries are sorted.** -/
theorem splice_sorted
    (hd : ws'.map wDat = (ws.take j).map wDat ++ ps.map pcDat ++ (ws.drop (j + 1)).map wDat)
    (hj : j < ws.length) (hm : 0 < ps.length) (hs : wsSorted ws)
    (hpc : ∀ a b, a < b → b < ps.length → go.GoStringLt (pcKey ps a) (pcKey ps b))
    (hlo : 0 < j → ¬ go.GoStringLt (pcKey ps 0) (wKey ws j))
    (hhi : j + 1 < ws.length → ∀ k < ps.length, go.GoStringLt (pcKey ps k) (wKey ws (j + 1))) :
    wsSorted ws' := by
  have hlen := splice_length hd hj
  have hpc0 : ∀ k < ps.length, ¬ go.GoStringLt (pcKey ps k) (pcKey ps 0) := by
    intro k hk
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · exact go.goStringLt_irrefl _
    · exact go.goStringLt_asymm (hpc 0 k hk0 hk)
  intro a b hab hb
  by_cases hbj : b < j
  · rw [splice_key_lt hd hj (by omega), splice_key_lt hd hj hbj]; exact hs a b hab (by omega)
  by_cases hbm : b < j + ps.length
  · have eb : b = j + (b - j) := by omega
    rw [eb, splice_key_mid hd hj (by omega)]
    by_cases haj : a < j
    · rw [splice_key_lt hd hj haj]
      have h1 : go.GoStringLt (wKey ws a) (pcKey ps 0) :=
        rk_lt_of_lt_le (hs a j haj hj) (hlo (by omega))
      rcases Nat.eq_zero_or_pos (b - j) with h0 | h0
      · rw [h0]; exact h1
      · exact go.goStringLt_trans h1 (hpc 0 _ h0 (by omega))
    · have ea : a = j + (a - j) := by omega
      rw [ea, splice_key_mid hd hj (by omega)]
      exact hpc _ _ (by omega) (by omega)
  · have eb : b = (b + 1 - ps.length) + ps.length - 1 := by omega
    rw [eb, splice_key_hi hd hj (by omega) (by omega)]
    by_cases haj : a < j
    · rw [splice_key_lt hd hj haj]; exact hs a _ (by omega) (by omega)
    by_cases ham : a < j + ps.length
    · have ea : a = j + (a - j) := by omega
      rw [ea, splice_key_mid hd hj (by omega)]
      have h1 := hhi (by omega) (a - j) (by omega)
      rcases Nat.lt_or_ge (j + 1) (b + 1 - ps.length) with h2 | h2
      · exact go.goStringLt_trans h1 (hs _ _ h2 (by omega))
      · rw [show b + 1 - ps.length = j + 1 by omega]; exact h1
    · have ea : a = (a + 1 - ps.length) + ps.length - 1 := by omega
      rw [ea, splice_key_hi hd hj (by omega) (by omega)]
      exact hs _ _ (by omega) (by omega)

/-- The pieces' first keys increase strictly. -/
theorem pieces_sorted {X : WX} {bl pl : Loc} {P : Pages} {hwm : Nat} {lo hi : Option (List w8)}
    {h : Nat} (hps : piecesOK X bl pl P hwm lo hi h ps) :
    ∀ a b, a < b → b < ps.length → go.GoStringLt (pcKey ps a) (pcKey ps b) := by
  have hstep : ∀ k, k + 1 < ps.length → go.GoStringLt (pcKey ps k) (pcKey ps (k + 1)) := by
    intro k hk
    have hx : ps[k]? = some ps[k] := List.getElem?_eq_getElem (by omega)
    obtain ⟨_, _, _, _, _, _, _, _, _, _, hf⟩ := hps.2.2 k _ hx
    have H := fTree_keyLt hf
    unfold childHi at H
    rw [if_pos hk] at H
    rw [pcKey_of_get hx]
    exact H _ rfl
  have : ∀ d a, a + d + 1 < ps.length → go.GoStringLt (pcKey ps a) (pcKey ps (a + d + 1)) := by
    intro d
    induction d with
    | zero => intro a ha; exact hstep a ha
    | succ d ih =>
      intro a ha
      exact go.goStringLt_trans (ih a (by omega)) (by
        rw [show a + (d + 1) + 1 = a + d + 1 + 1 by omega]; exact hstep _ (by omega))
  intro a b hab hb
  have := this (b - a - 1) a (by omega)
  rwa [show a + (b - a - 1) + 1 = b by omega] at this

end keys

end Spill

end bbolt
end EtcdGrove
end Perennial

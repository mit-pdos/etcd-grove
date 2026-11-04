/-
`flView` and `covU` after a position's page is freed (U8b, `Rebalance/RblXSteps.lean`): when the
records lose the position `E` of bucket `bl` (its extent `(E, N)`) and keep every other
position's extent, and the writer frees `E`'s pages (`freePages`), the covered slots are those
before but `E`'s, which only `E` covered (`covU`) and which are now pending (`flView_free`).
-/
module

public import Proof.go_etcd_io.bbolt.Rebalance.RblX

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section fl
variable [GooseExts]

/-- `lCovers` by its witnesses. -/
theorem lCovers_iff (X : WX) (s : Nat) : lCovers X s ↔ ∃ c, coverW X s c := by
  constructor
  · rintro (⟨bl, e, hne, he, h1, h2⟩ | ⟨n, v, h1, h2, h3⟩)
    · obtain ⟨pid, hp, hx⟩ := List.mem_filterMap.1 he
      exact ⟨.pos bl pid, hne, hp, e, hx, h1, h2⟩
    · exact ⟨.bkt n, v, h1, h2, h3⟩
  · rintro ⟨c, hc⟩
    cases c with
    | pos bl pid =>
      obtain ⟨hne, hp, e, hx, h1, h2⟩ := hc
      exact Or.inl ⟨bl, e, hne, List.mem_filterMap.2 ⟨pid, hp, hx⟩, h1, h2⟩
    | bkt n =>
      obtain ⟨v, h1, h2, h3⟩ := hc
      exact Or.inr ⟨n, v, h1, h2, h3⟩

theorem runIds_toNat (id : w64) (n : Nat) (hn : id.toNat + n < 2 ^ 64) (x : w64)
    (hx : x ∈ runIds id n) : ∃ j, j < n ∧ x.toNat = id.toNat + j := by
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hx
  refine ⟨j, List.mem_range.1 hj, ?_⟩
  have hj' := List.mem_range.1 hj
  rw [BitVec.toNat_add]
  have : (W64 (j : Int)).toNat = j := by simp only [W64, BitVec.toNat_ofInt]; omega
  rw [this]; omega

theorem runIds_nodup (id : w64) (n : Nat) (hn : id.toNat + n < 2 ^ 64) : (runIds id n).Nodup := by
  unfold runIds
  apply List.pairwise_map.2
  apply (List.nodup_range).imp_of_mem
  intro a b ha hb hab he
  have ha' := List.mem_range.1 ha
  have hb' := List.mem_range.1 hb
  have := congrArg BitVec.toNat he
  rw [BitVec.toNat_add, BitVec.toNat_add] at this
  have e1 : (W64 (a : Int)).toNat = a := by simp only [W64, BitVec.toNat_ofInt]; omega
  have e2 : (W64 (b : Int)).toNat = b := by simp only [W64, BitVec.toNat_ofInt]; omega
  rw [e1, e2] at this
  apply hab
  omega

/-- **`flView` and `covU` after the position `E` of `bl` is freed** (see the module doc). -/
theorem flView_free (X X' : WX) (fl : FLPg) (bl : Loc) (E : w64) (N : Nat) (txid : w64)
    (hfv : flView X fl) (hu : covU X)
    (hv : X'.v = X.v)
    (hdom : ∀ c, (X'.t.bs !! c).isSome = (X.t.bs !! c).isSome)
    (hbl : X.t.bs !! bl ≠ none)
    (hoth : ∀ c, c ≠ bl → X'.positions c = X.positions c ∧ X'.posExtent c = X.posExtent c)
    (hpos1 : ∀ q ∈ X'.positions bl, q ∈ X.positions bl ∧ q ≠ E)
    (hpos2 : ∀ q ∈ X.positions bl, q ≠ E → q ∈ X'.positions bl)
    (hext : ∀ q, q ≠ E → X'.posExtent bl q = X.posExtent bl q)
    (hE : E ∈ X.positions bl) (hEx : X.posExtent bl E = some (E, N))
    (hpgE : ∃ pg, X.v.pages !! E.toNat = some pg)
    (hre : rootEnts X' = rootEnts X) (hbk : bktLoc X' = bktLoc X)
    (hcan : fl.canFree txid E N) (h62 : E.toNat + N ≤ 2 ^ 62)
    (hlen : ∀ t p, fl.pending !! t = some p → p.ids.length = p.alloctx.length)
    (htx : X.v.txid < txid.toNat) :
    flView X' (fl.freePages txid E N) ∧ covU X' := by
  have hN64 : E.toNat + N < 2 ^ 64 := hcan.2.1
  have hne : ∀ c, (X'.t.bs !! c ≠ none) ↔ (X.t.bs !! c ≠ none) := by
    intro c; rw [Option.ne_none_iff_isSome, Option.ne_none_iff_isSome, hdom]
  -- witnesses
  have hback : ∀ s c, coverW X' s c → coverW X s c ∧ c ≠ .pos bl E := by
    intro s c hc
    cases c with
    | pos c q =>
      obtain ⟨h1, h2, e, h3, h4, h5⟩ := hc
      by_cases hcb : c = bl
      · subst hcb
        obtain ⟨hq, hqE⟩ := hpos1 q h2
        rw [hext q hqE] at h3
        exact ⟨⟨(hne c).1 h1, hq, e, h3, h4, h5⟩, fun h => by cases h; exact hqE rfl⟩
      · obtain ⟨p1, p2⟩ := hoth c hcb
        rw [p1] at h2; rw [p2] at h3
        exact ⟨⟨(hne c).1 h1, h2, e, h3, h4, h5⟩, fun h => by cases h; exact hcb rfl⟩
    | bkt n =>
      obtain ⟨v, h1, h2, h3⟩ := hc
      rw [hre] at h1; rw [hbk] at h2; rw [hv] at h3
      exact ⟨⟨v, h1, h2, h3⟩, fun h => by cases h⟩
  have hfwd : ∀ s c, coverW X s c → c ≠ .pos bl E → coverW X' s c := by
    intro s c hc hcE
    cases c with
    | pos c q =>
      obtain ⟨h1, h2, e, h3, h4, h5⟩ := hc
      by_cases hcb : c = bl
      · subst hcb
        have hqE : q ≠ E := fun h => hcE (by rw [h])
        refine ⟨(hne c).2 h1, hpos2 q h2 hqE, e, ?_, h4, h5⟩
        rw [hext q hqE]; exact h3
      · obtain ⟨p1, p2⟩ := hoth c hcb
        exact ⟨(hne c).2 h1, by rw [p1]; exact h2, e, by rw [p2]; exact h3, h4, h5⟩
    | bkt n =>
      obtain ⟨v, h1, h2, h3⟩ := hc
      exact ⟨v, by rw [hre]; exact h1, by rw [hbk]; exact h2, by rw [hv]; exact h3⟩
  have hEw : ∀ s, coverW X s (.pos bl E) ↔ E.toNat ≤ s ∧ s < E.toNat + N := by
    intro s
    constructor
    · rintro ⟨-, -, e, he, h1, h2⟩
      rw [hEx] at he; cases he; exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨hbl, hE, (E, N), hEx, h1, h2⟩
  have hcov : ∀ s, lCovers X' s ↔ lCovers X s ∧ ¬ (E.toNat ≤ s ∧ s < E.toNat + N) := by
    intro s
    rw [lCovers_iff, lCovers_iff]
    constructor
    · rintro ⟨c, hc⟩
      obtain ⟨hc0, hcE⟩ := hback s c hc
      exact ⟨⟨c, hc0⟩, fun hr => hcE (hu s c _ hc0 ((hEw s).2 hr))⟩
    · rintro ⟨⟨c, hc⟩, hr⟩
      refine ⟨c, hfwd s c hc fun h => ?_⟩
      subst h; exact hr ((hEw s).1 hc)
  obtain ⟨hf1, ⟨hm1, hm2⟩, hnd, h62'⟩ := hfv
  refine ⟨⟨fun s hs => ?_, ⟨fun id pg hpg a ha => ?_, fun s hs => ?_⟩, ?_, ?_⟩, ?_⟩
  · rw [hv] at hs
    rw [hcov, pendSlots_freePages fl txid E N hN64, hf1 s hs]
    exact not_or.symm
  · rw [hv] at hpg ⊢
    simp only [FLPg.freePages] at ha
    rw [GMap.lookup_delete_iff] at ha
    split at ha
    · cases ha
    · exact hm1 id pg hpg a ha
  · rw [hv] at hs ⊢
    obtain ⟨h2, hfr, hp⟩ := hm2 s hs
    refine ⟨h2, hfr, fun t pd i hpd hi => ?_⟩
    rcases freePages_pending_lookup fl txid E N t pd hpd with ⟨-, hpd'⟩ | ⟨rfl, P, hP, rfl⟩
    · exact hp t pd i hpd' hi
    · refine ⟨?_, htx⟩
      have hPl : P.ids.length = P.alloctx.length := by
        cases h : fl.pending !! t with
        | none => rw [h] at hP; simp at hP; rw [← hP]
        | some P0 => rw [h] at hP; simp at hP; rw [← hP]; exact hlen t P0 h
      simp only at hi ⊢
      by_cases hil : i < P.ids.length
      · rw [List.getElem?_append_left hil] at hi
        have hPs : fl.pending !! t = some P := by
          cases h : fl.pending !! t with
          | none => rw [h] at hP; simp at hP; rw [← hP] at hil; simp at hil
          | some P0 => rw [h] at hP; simp at hP; rw [hP]
        have := (hp t P i hPs hi).1
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega)]
        rw [List.getD_eq_getElem?_getD] at this
        exact this
      · rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]
        rw [List.getElem?_replicate]
        split
        · simp only [Option.getD_some]
          cases ha : fl.allocs !! E with
          | none => simp
          | some a =>
            simp only [Option.getD_some]
            obtain ⟨pg, hpg⟩ := hpgE
            exact hm1 E.toNat pg hpg a (by simp [W64]; exact ha)
        · simp
  · -- distinct ids
    unfold FLPg.allIds at hnd ⊢
    have hperm := pendingIds_freePages_perm fl txid E N
    have hfree : (fl.freePages txid E N).free = fl.free := rfl
    rw [hfree]
    have hp' : (fl.free ++ (fl.freePages txid E N).pendingIds).Perm
        ((fl.free ++ fl.pendingIds) ++ runIds E N) := by
      rw [List.append_assoc]; exact List.Perm.append_left _ hperm
    apply hp'.nodup_iff.2
    apply List.nodup_append.2
    refine ⟨hnd, runIds_nodup E N hN64, fun a ha b hb hab => ?_⟩
    subst hab
    exact hcan.2.2.1 a hb ha
  · intro x hx
    unfold FLPg.allIds at hx h62'
    have hperm := pendingIds_freePages_perm fl txid E N
    have hfree : (fl.freePages txid E N).free = fl.free := rfl
    rw [hfree] at hx
    rcases List.mem_append.1 hx with h | h
    · exact h62' x (List.mem_append_left _ h)
    · rcases List.mem_append.1 (hperm.mem_iff.1 h) with h | h
      · exact h62' x (List.mem_append_right _ h)
      · obtain ⟨j, hj, hxj⟩ := runIds_toNat E N hN64 x h
        omega
  · intro s c1 c2 h1 h2
    exact hu s c1 c2 (hback s c1 h1).1 (hback s c2 h2).1

end fl

end bbolt
end EtcdGrove
end Perennial

/-
What `Cursor.seek` returns, from where its search ends (`ShapeRoute.lean`'s `kseek`): the
path's last position (`kseek_last`, `wpath_last` with the leaf's index), and, at it, the entries
with the searched key are the one returned (`seek_node_key`, `seek_page_key`: `PathFlags.lean`'s
`posKey`, `keySrcIs`), since the leaf's keys increase and its index is the first not below the key.
-/
module

public import Proof.go_etcd_io.bbolt.ShapeRoute
public import Proof.go_etcd_io.bbolt.PathFlags

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section seek
variable [ext : FfiSyntax]

/-- Among increasing keys, the key `kb` can only be at its search index. -/
theorem keysIdx_eq {L : List (List w8)} {kb : List w8} {i j : Nat} (hs : keysSorted L)
    (hk : keysIdx L kb i) (hj : L[j]? = some kb) : j = i := by
  obtain ⟨-, hbelow, hat⟩ := hk
  rcases Nat.lt_trichotomy j i with hlt | heq | hgt
  · exact absurd (hbelow j kb hlt hj) (goStringLt_irrefl_r kb)
  · exact heq
  · have hil : i < L.length := by
      have := (List.getElem?_eq_some_iff.1 hj).1; omega
    exact absurd (hs i j _ kb hgt (List.getElem?_eq_getElem hil) hj)
      (hat _ (List.getElem?_eq_getElem hil))

/-- A leaf page's keys (`keysAt`) are its leaf keys. -/
theorem pageKeys_leaf' (pg : List w8) (h : pageFlags pg = leafPageFlag) :
    (List.range (pageCount pg)).map (pageKey pg) = (List.range (pageCount pg)).map (leafKey pg) := by
  apply List.map_congr_left; intro i _; simp [pageKey, h]

/-- The last position of a search's path (`wpath_last`), with the leaf's index (`kseek`); an
entry property there holds at the path's end (`pathKey`). -/
theorem kseek_last (W : WView) (hwm : Nat) (bl : Loc) (B : BRec) (kb : List w8)
    (hc : bktClean W hwm bl B) :
    ∀ (es : List elemRef) (pid : w64), wpath W B pid es → kseek W B kb pid es → posOK W hwm B pid →
    ∃ pid' r ks, es.getLast? = some r ∧ refAt W B pid' r ∧ posOK W hwm B pid' ∧
      kidsAt W B pid' = some (true, ks) ∧ 0 ≤ sint.Z r.index' ∧
      (∃ L, keysAt W B pid' = some L ∧ keysIdx L kb (sint.Z r.index').toNat) ∧
      (∀ P, posKey W B pid' kb P → pathKey W B kb P pid es) := by
  intro es
  induction es with
  | nil => intro pid h; exact absurd h (by simp [wpath])
  | cons r rs ih =>
    intro pid h hk hpos
    cases rs with
    | nil =>
      obtain ⟨hr, hi, ks, hkd⟩ := h
      exact ⟨pid, r, ks, rfl, hr, hpos, hkd, hi, hk, fun P hP => hP⟩
    | cons r2 rs' =>
      obtain ⟨hr, hi, ks, c, hkd, hc', hrest⟩ := h
      obtain ⟨cs, c', hkd2, hc2, hrest2⟩ := hk
      rw [hkd] at hkd2
      obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj hkd2)
      rw [hc'] at hc2
      cases hc2
      have hcpos : posOK W hwm B c := by
        -- the child's position is OK (`wpath_last`'s induction step)
        unfold kidsAt at hkd
        rcases hpos.2 with ⟨l, rr, hres, hrr⟩ | ⟨hres, hpg⟩
        · rw [hres] at hkd
          simp only [hrr, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hkd
          obtain ⟨hleaf, rfl⟩ := hkd
          simp only [hleaf, Bool.false_eq_true, ↓reduceIte, List.getElem?_map] at hc'
          obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.1 hc'
          exact posOK_node_child W hwm bl B l rr hc hrr hleaf _ w hw
        · rw [hres] at hkd
          rcases hpg with ⟨h0, -, -, -, hinl⟩ | ⟨hr0, hwf, hfree⟩
          · have hp0 := hpos.1 h0
            simp only [wpageAt, h0, hp0, ↓reduceIte, Option.map_some, Option.some.injEq,
              Prod.mk.injEq] at hkd
            obtain ⟨hleaf, -⟩ := hkd
            exfalso; revert hleaf; simp [hinl.2.1]
          · obtain ⟨pg, hpg, hpa, -, -⟩ := posOK_page W hwm B pid hr0 hres hpos
            simp only [hpa, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hkd
            obtain ⟨hleaf, rfl⟩ := hkd
            obtain ⟨-, -, -, hkind⟩ := treeWF_page _ _ _ pg hwf hpg
            rcases hkind with ⟨hfl, -⟩ | ⟨hfl, -, hkids⟩
            · exfalso; revert hleaf; simp [hfl]
            · rw [if_neg (by rw [hfl]; unfold branchPageFlag leafPageFlag; decide),
                List.getElem?_map] at hc'
              obtain ⟨i, hi', rfl⟩ := Option.map_eq_some_iff.1 hc'
              have hil := (List.mem_range.1 (List.mem_of_getElem? hi'))
              exact posOK_page_child W hwm B pid pg hr0 hpg hfl hkids hfree _ hil
      obtain ⟨pid', r', ks', hl, h1, h2, h3, h4, h5, h6⟩ := ih c hrest hrest2 hcpos
      exact ⟨pid', r', ks', by simpa using hl, h1, h2, h3, h4, h5,
        fun P hP => ⟨ks, c, hkd, hc', h6 P hP⟩⟩

/-- At a leaf node, `seek`'s result (`nodeKV` at the search index) is the entry with the key. -/
theorem seek_node_key (W : WView) (B : BRec) (pid : w64) (l : Loc) (r : NRec) (kb : List w8)
    (idx : w64) (hres : resolve B pid = some l) (hr : B.ns !! l = some r)
    (hlen : r.ins.length = r.ws.length) (hlive : wsLive r.ws) (hsort : wsSorted r.ws)
    (hfl : ∀ it w, r.ins[(sint.Z idx).toNat]? = some it → r.ws[(sint.Z idx).toNat]? = some w →
      it.flags' = w.flags)
    (h0 : 0 ≤ sint.Z idx) (hk : keysIdx (r.ws.map WEntry.key) kb (sint.Z idx).toNat) :
    ∃ kbs, keySrcIs W B (nodeKV r.ins (sint.Z idx)).1 kbs ∧
      (∀ w, r.ws[(sint.Z idx).toNat]? = some w →
        ¬ (r.ins.length = 0 ∨ (r.ins.length : Int) ≤ sint.Z idx) → w.key = kbs) ∧
      posKey W B pid kb (fun fl => fl = (nodeKV r.ins (sint.Z idx)).2.2 ∧ kbs = kb) := by
  have HS : keysSorted (r.ws.map WEntry.key) := keysSorted_fn (keysFn_ws r.ws) hsort
  have hcases : ∀ w ∈ r.ws, w.key = kb → ∃ it w', r.ins[(sint.Z idx).toNat]? = some it ∧
      r.ws[(sint.Z idx).toNat]? = some w' ∧ w' = w := by
    intro w hw hwk
    obtain ⟨j, hj, hjw⟩ := List.getElem_of_mem hw
    have hj' : (r.ws.map WEntry.key)[j]? = some kb := by
      rw [List.getElem?_map, List.getElem?_eq_getElem hj, hjw]; simp [hwk]
    have := keysIdx_eq HS hk hj'
    subst this
    exact ⟨_, _, List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem hj, hjw⟩
  by_cases hi : (sint.Z idx).toNat < r.ws.length
  · obtain ⟨it, hit⟩ : ∃ it, r.ins[(sint.Z idx).toNat]? = some it :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨w, hw⟩ : ∃ w, r.ws[(sint.Z idx).toNat]? = some w := ⟨_, List.getElem?_eq_getElem hi⟩
    have hkv : nodeKV r.ins (sint.Z idx) = (it.key', it.value', it.flags') := by
      unfold nodeKV
      rw [if_neg (by omega), hit]
    rw [hkv]
    refine ⟨w.key, Or.inr (Or.inl ⟨l, r, _, it, w, hr, hit, hw, rfl,
      (hlive w (List.mem_of_getElem? hw)).1, rfl⟩),
      fun w' hw' _ => by rw [hw] at hw'; cases hw'; rfl, ?_, ?_⟩
    · intro l' r' hres' hr' w' hw' hwk
      rw [hres] at hres'; cases hres'
      rw [hr] at hr'; cases hr'
      obtain ⟨it', w'', hit', hw'', rfl⟩ := hcases w' hw' hwk
      rw [hit] at hit'; cases hit'
      rw [hw] at hw''; cases hw''
      exact ⟨(hfl _ _ hit hw).symm, hwk⟩
    · intro hn; rw [hres] at hn; cases hn
  · have hkv : (nodeKV r.ins (sint.Z idx)).1 = slice.nil := by
      unfold nodeKV; rw [if_pos (by omega)]
    rw [hkv]
    refine ⟨[], Or.inl ⟨rfl, rfl⟩, fun w' hw' hc => absurd hc (by omega), ?_, ?_⟩
    · intro l' r' hres' hr' w' hw' hwk
      rw [hres] at hres'; cases hres'
      rw [hr] at hr'; cases hr'
      obtain ⟨it', w'', hit', hw'', -⟩ := hcases w' hw' hwk
      exact absurd (List.getElem?_eq_some_iff.1 hw'').1 hi
    · intro hn; rw [hres] at hn; cases hn

/-- At a leaf page, `seek`'s result (`kvResult` at the search index) is the entry with the key. -/
theorem seek_page_key (W : WView) (B : BRec) (pid : w64) (p : Loc) (pg : List w8) (kb : List w8)
    (idx : w64) (hres : resolve B pid = none) (hpa : wpageAt W B pid = some (p, pg))
    (hinl : B.ib.root' = W64 0 → B.bv.page' ≠ null ∧ B.isrc ≠ Src.stale) (hlen : 16 ≤ pg.length)
    (hwf : leafWF pg pg.length) (hfl : pageFlags pg = leafPageFlag)
    (h0 : 0 ≤ sint.Z idx)
    (hk : keysIdx ((List.range (pageCount pg)).map (pageKey pg)) kb (sint.Z idx).toNat)
    (hu : ∀ pid' pg', wpageAt W B pid' = some (p, pg') → pg' = pg) :
    ∃ kbs, keySrcIs W B (kvResult p pg (sint.Z idx)).1 kbs ∧
      (∀ pid' pg', wpageAt W B pid' = some (p, pg') →
        ¬ (pageCount pg' = 0 ∨ (pageCount pg' : Int) ≤ sint.Z idx) →
        leafKey pg' (sint.Z idx).toNat = kbs) ∧
      posKey W B pid kb (fun fl => fl = (kvResult p pg (sint.Z idx)).2.2 ∧ kbs = kb) := by
  rw [pageKeys_leaf' pg hfl] at hk
  have HF := keysFn_range (pageCount pg) (leafKey pg)
  have HS : keysSorted ((List.range (pageCount pg)).map (leafKey pg)) :=
    keysSorted_fn HF hwf.2.2.2
  have hj : ∀ j, j < pageCount pg → leafKey pg j = kb → j = (sint.Z idx).toNat := fun j hj hjk =>
    keysIdx_eq HS hk (by rw [HF.2 j hj, hjk])
  by_cases hi : (sint.Z idx).toNat < pageCount pg
  · have hc : ¬ (pageCount pg = 0 ∨ (pageCount pg : Int) ≤ sint.Z idx) := by omega
    have hb := (hwf.2.2.1 _ hi).1
    refine ⟨leafKey pg (sint.Z idx).toNat, ?_, fun pid' pg' h _ => by rw [hu pid' pg' h],
      fun _ _ hn => absurd hn (by rw [hres]; simp), ?_⟩
    · unfold kvResult; rw [if_neg hc]
      exact Or.inr (Or.inr ⟨pid, p, pg, elemOff (sint.Z idx).toNat + leafPos pg (sint.Z idx).toNat,
        leafKsize pg (sint.Z idx).toNat, hpa, hinl, hlen, by omega, leAt_lt _ _ 4, rfl, rfl⟩)
    · intro _ lp hlp j hjc hjk
      rw [hpa] at hlp; cases hlp; simp only at hjc hjk
      have := hj j hjc hjk
      subst this
      unfold kvResult; rw [if_neg hc]
      exact ⟨rfl, hjk⟩
  · have hc : pageCount pg = 0 ∨ (pageCount pg : Int) ≤ sint.Z idx := by omega
    refine ⟨[], ?_, fun pid' pg' h hc' => absurd (hu pid' pg' h ▸ hc') (by omega),
      fun _ _ hn => absurd hn (by rw [hres]; simp), ?_⟩
    · unfold kvResult; rw [if_pos hc]; exact Or.inl ⟨rfl, rfl⟩
    · intro _ lp hlp j hjc hjk
      rw [hpa] at hlp; cases hlp; simp only at hjc hjk
      have := hj j hjc hjk
      omega

end seek

end bbolt
end EtcdGrove
end Perennial

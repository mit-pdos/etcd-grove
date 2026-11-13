/- Lean-first (no Rocq counterpart).

# Lemmas for `cutCommit_pure` (W2, `notes/wal-fsext-plan.md`, "W2 implementation log")

Pure. The pieces of a cut's rename commit (`CutCommit.lean`) that do not depend on the layout:
- the rename's entry writes `tmp` and `bt` of `j` (`renFileEnt_writes`);
- the claims after the commit (`replClaim c0 c1 cl`): the replacement or an old claim other than
  `c0` (`mem_replClaim_cases`); a claim once in `cl`, neither, is once after (`claimOnce_repl_other`);
- the WAL directory's claim is the only one of `j` on all names but non-`.wal` ones
  (`walClaim_eq`);
- the `.wal` names: one per file when the files are distinct (`walName_unique`); a `.wal` name
  above every other added at the end (`walInos_insert_last`);
- a crash of the claims after the commit is one of the claims before (`regionCrashed_cut`: dropping
  the rename, the same tree; keeping it, the tree without `bt`, `treeDel`);
- what reads no `(j, bt)` is unchanged by it: another directory's entries, a successful lookup
  (`lookupH_treeDel`), another WAL's crash condition (`crashOkA_cut_other`).
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CreateKeys
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CutTail

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Fs WalEnc

section pure
variable [GooseExts]

/-! ## The rename's entry -/

theorem renFileEnt_writes (j : Ino) (tmp bt : GoString) (i : Ino) (h : NamesH) (s : Nat) (j' : Ino)
    (b : GoString) :
    (renFileEnt j tmp j bt i h s).op.Writes j' b ↔ j' = j ∧ (b = tmp ∨ b = bt) := by
  unfold renFileEnt MetaOp.Writes MetaOp.slots
  constructor
  · rintro (h | ⟨j0, b0, h⟩)
    · simp only [List.mem_cons, Prod.mk.injEq, List.mem_nil_iff, or_false] at h
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨rfl, Or.inl rfl⟩
      · exact ⟨rfl, Or.inr rfl⟩
    · cases h
  · rintro ⟨rfl, rfl | rfl⟩
    · left; simp
    · left; simp

/-! ## The claims after the commit -/

open Classical in
theorem mem_replClaim_cases {c0 c1 c : Claim} {cl : List Claim} (h : c ∈ replClaim c0 c1 cl) :
    c = c1 ∨ (c ∈ cl ∧ c ≠ c0) := by
  unfold replClaim at h
  obtain ⟨c', hc', rfl⟩ := List.mem_map.1 h
  by_cases e : c' = c0
  · left; simp [e]
  · right; simp only [if_neg e]; exact ⟨hc', e⟩

open Classical in
theorem mem_replClaim_of_ne {c0 c1 c : Claim} {cl : List Claim} (h : c ∈ cl) (hne : c ≠ c0) :
    c ∈ replClaim c0 c1 cl := by
  have := mem_replClaim (c0 := c0) (c1 := c1) h
  rwa [if_neg hne] at this

theorem mem_replClaim_new {c0 c1 : Claim} {cl : List Claim} (h : c0 ∈ cl) :
    c1 ∈ replClaim c0 c1 cl := by
  classical
  have := mem_replClaim (c0 := c0) (c1 := c1) h
  rwa [if_pos rfl] at this

/-- A claim once in `cl`, neither the replaced one nor its replacement, is once after. -/
theorem claimOnce_repl_other {c c0 c1 : Claim} {cl : List Claim} (h : ClaimOnce c cl)
    (h0 : c ≠ c0) (h1 : c ≠ c1) : ClaimOnce c (replClaim c0 c1 cl) := by
  classical
  obtain ⟨l1, l2, rfl, hn1, hn2⟩ := h
  have hf : ∀ l : List Claim, c ∉ l → c ∉ l.map (fun x => if x = c0 then c1 else x) := by
    intro l hl hm
    obtain ⟨y, hy, e⟩ := List.mem_map.1 hm
    by_cases hy0 : y = c0
    · rw [if_pos hy0] at e; exact h1 e.symm
    · rw [if_neg hy0] at e; subst e; exact hl hy
  refine ⟨l1.map (fun x => if x = c0 then c1 else x), l2.map (fun x => if x = c0 then c1 else x),
    ?_, hf l1 hn1, hf l2 hn2⟩
  unfold replClaim
  rw [List.map_append, List.map_cons, if_neg h0]

/-- A `.wal` name (for the `except` sets of names without one). -/
theorem walNameP_wal : walNameP go!".wal" = true := by decide

theorem except_mem_wal {X : List GoString} (hX : ∀ b ∈ X, walNameP b = false) :
    (NameSet.except X).Mem go!".wal" := fun hb => by
  have h := walNameP_wal
  rw [hX _ hb] at h; cases h

/-- **The WAL directory's claim is its only claim on all names but non-`.wal` ones** (the others of
`j` hold no `.wal` name). -/
theorem walClaim_eq {cl : List Claim} {j : Ino} {X : List GoString} {hj : NamesH}
    (hexcl : ∀ c' ∈ cl, c' ≠ (j, NameSet.except X, hj) → c'.1 = j → ∀ b, walNameP b = true →
      ¬ c'.2.1.Mem b)
    {X' : List GoString} {hj' : NamesH} (hX' : ∀ b ∈ X', walNameP b = false)
    (hm : (j, NameSet.except X', hj') ∈ cl) : (j, NameSet.except X', hj') = (j, NameSet.except X, hj) := by
  refine Classical.byContradiction fun hne => ?_
  exact hexcl _ hm hne rfl _ walNameP_wal (except_mem_wal hX')

/-! ## The `.wal` names -/

theorem filterMap_inj_of_nodup {α β : Type} {f : α → Option β} :
    ∀ {l : List α}, l.Nodup → (l.filterMap f).Nodup → ∀ {a b : α} {y : β}, a ∈ l → b ∈ l →
      f a = some y → f b = some y → a = b
  | [], _, _, _, _, _, ha, _, _, _ => by cases ha
  | x :: l, hl, hfl, a, b, y, ha, hb, hfa, hfb => by
    rw [List.nodup_cons] at hl
    have hmem : ∀ c ∈ l, f c = some y → y ∈ l.filterMap f := fun c hc hfc =>
      List.mem_filterMap.2 ⟨c, hc, hfc⟩
    rw [List.filterMap_cons] at hfl
    rcases List.mem_cons.1 ha with rfl | ha'
    · rcases List.mem_cons.1 hb with rfl | hb'
      · rfl
      · rw [hfa] at hfl
        exact absurd (hmem b hb' hfb) (List.nodup_cons.1 hfl).1
    · rcases List.mem_cons.1 hb with rfl | hb'
      · rw [hfb] at hfl
        exact absurd (hmem a ha' hfa) (List.nodup_cons.1 hfl).1
      · have hfl' : (l.filterMap f).Nodup := by
          cases hx : f x with
          | none => rw [hx] at hfl; exact hfl
          | some z => rw [hx] at hfl; exact (List.nodup_cons.1 hfl).2
        exact filterMap_inj_of_nodup hl.2 hfl' ha' hb' hfa hfb

theorem walNames_nodup (E : Ents) : (walNames E).Nodup := by
  unfold walNames
  exact (List.mergeSort_perm _ _).nodup_iff.2 ((GMap.toList_keys_nodup E).filter _)

theorem mem_walNames {E : Ents} {b : GoString} {e : Node} (hb : walNameP b = true)
    (he : E !! b = some e) : b ∈ walNames E := by
  unfold walNames
  refine (List.mergeSort_perm _ _).mem_iff.2 (List.mem_filter.2 ⟨?_, hb⟩)
  exact List.mem_map.2 ⟨(b, e), (GMap.mem_toList _ _ _).2 he, rfl⟩

/-- **Distinct files, one `.wal` name each**: two `.wal` names of the same file are one. -/
theorem walName_unique {E : Ents} (hnd : (walInos E).Nodup) {b1 b2 : GoString} {i : Ino}
    (h1 : walNameP b1 = true) (h2 : walNameP b2 = true) (e1 : E !! b1 = some (.file i))
    (e2 : E !! b2 = some (.file i)) : b1 = b2 := by
  unfold walInos at hnd
  refine filterMap_inj_of_nodup (walNames_nodup E) hnd (mem_walNames h1 e1) (mem_walNames h2 e2)
    (y := i) ?_ ?_
  · simp [e1]
  · simp [e2]

/-- **A `.wal` name above every other added**: its file comes last. -/
theorem walInos_insert_last {E : Ents} {bt : GoString} {i : Ino} (hbt : walNameP bt = true)
    (hnone : E !! bt = none)
    (hlt : ∀ b e, walNameP b = true → E !! b = some e → go.GoStringLt b bt) :
    walInos (<[bt := Node.file i]> E) = walInos E ++ [i] := by
  classical
  have htr : ∀ a b c : GoString, decide (go.GoStringLt a b ∨ a = b) = true →
      decide (go.GoStringLt b c ∨ b = c) = true → decide (go.GoStringLt a c ∨ a = c) = true := by
    intro a b c h1 h2
    simp only [decide_eq_true_eq] at h1 h2 ⊢
    rcases h1 with h1 | rfl <;> rcases h2 with h2 | rfl
    · exact Or.inl (go.goStringLt_trans h1 h2)
    · exact Or.inl h1
    · exact Or.inl h2
    · exact Or.inr rfl
  have hto : ∀ a b : GoString,
      (decide (go.GoStringLt a b ∨ a = b) || decide (go.GoStringLt b a ∨ b = a)) = true := by
    intro a b
    by_cases h1 : go.GoStringLt a b
    · simp [h1]
    by_cases h2 : go.GoStringLt b a
    · simp [h2]
    simp [go.goStringLt_eq_of_not_lt h1 h2]
  have hsortE : (walNames E).Pairwise (fun a b => decide (go.GoStringLt a b ∨ a = b) = true) :=
    List.pairwise_mergeSort htr hto _
  have hnames : walNames (<[bt := Node.file i]> E) = walNames E ++ [bt] := by
    have hsort' : (walNames E ++ [bt]).Pairwise
        (fun a b => decide (go.GoStringLt a b ∨ a = b) = true) := by
      refine List.pairwise_append.2 ⟨hsortE, by simp, fun a ha b hb => ?_⟩
      simp only [List.mem_singleton] at hb; subst hb
      have ha' : a ∈ ((GMap.toList E).map (·.1)).filter walNameP := by
        unfold walNames at ha; exact List.mem_mergeSort.1 ha
      obtain ⟨⟨⟨a', e⟩, hm, rfl⟩, hw⟩ := by simpa only [List.mem_filter, List.mem_map] using ha'
      simp only [decide_eq_true_eq]
      exact Or.inl (hlt a' e hw ((GMap.mem_toList _ _ _).1 hm))
    have hperm : (walNames (<[bt := Node.file i]> E)).Perm (walNames E ++ [bt]) := by
      have hnd1 := walNames_nodup (<[bt := Node.file i]> E)
      have hnd2 : (walNames E ++ [bt]).Nodup := by
        refine List.nodup_append.2 ⟨walNames_nodup E, by simp, fun a ha b hb => ?_⟩
        simp only [List.mem_singleton] at hb
        rw [hb]
        intro hab
        rw [hab] at ha
        unfold walNames at ha
        obtain ⟨⟨⟨a', e⟩, hm, rfl⟩, -⟩ := by
          simpa only [List.mem_filter, List.mem_map] using List.mem_mergeSort.1 ha
        rw [(GMap.mem_toList _ _ _).1 hm] at hnone; cases hnone
      refine (List.perm_ext_iff_of_nodup hnd1 hnd2).2 (fun b => ?_)
      unfold walNames
      simp only [List.mem_append, List.mem_singleton, List.mem_mergeSort, List.mem_filter,
        List.mem_map]
      constructor
      · rintro ⟨⟨⟨b', e⟩, hm, rfl⟩, hw⟩
        rw [GMap.mem_toList] at hm
        by_cases hb : b' = bt
        · right; exact hb
        · left
          rw [GMap.lookup_insert_ne _ _ (Ne.symm hb)] at hm
          exact ⟨⟨(b', e), (GMap.mem_toList _ _ _).2 hm, rfl⟩, hw⟩
      · rintro (⟨⟨⟨b', e⟩, hm, rfl⟩, hw⟩ | hbe)
        · rw [GMap.mem_toList] at hm
          have hb : b' ≠ bt := by rintro rfl; rw [hm] at hnone; cases hnone
          exact ⟨⟨(b', e), (GMap.mem_toList _ _ _).2 (by
            rw [GMap.lookup_insert_ne _ _ (Ne.symm hb)]; exact hm), rfl⟩, hw⟩
        · rw [hbe]
          exact ⟨⟨(bt, .file i), (GMap.mem_toList _ _ _).2 (GMap.lookup_insert_eq _ _ _), rfl⟩, hbt⟩
    refine List.Perm.eq_of_pairwise (le := fun a b => decide (go.GoStringLt a b ∨ a = b) = true) ?_
      (List.pairwise_mergeSort htr hto _) hsort' hperm
    intro a b _ _ h1 h2
    simp only [decide_eq_true_eq] at h1 h2
    rcases h1 with h1 | h1
    · rcases h2 with h2 | h2
      · exact absurd h2 (go.goStringLt_asymm h1)
      · exact h2.symm
    · exact h1
  unfold walInos
  rw [hnames, List.filterMap_append]
  congr 1
  · refine filterMap_congr' (fun b hb => ?_)
    have hne : bt ≠ b := by
      rintro rfl
      unfold walNames at hb
      obtain ⟨⟨⟨a', e⟩, hm, rfl⟩, -⟩ := by
        simpa only [List.mem_filter, List.mem_map] using List.mem_mergeSort.1 hb
      rw [(GMap.mem_toList _ _ _).1 hm] at hnone; cases hnone
    rw [GMap.lookup_insert_ne _ _ hne]
  · simp

/-! ## Crashes of the claims after the commit -/

theorem entsOf_treeDel_ne (m' : Tree) {j j' : Ino} (bt : GoString) (h : j' ≠ j) :
    entsOf (treeDel m' j bt) j' = entsOf m' j' := by
  apply GMap.ext; intro b
  rw [entsOf_entry, entsOf_entry, treeDel_entry]
  simp [h]

/-- **A crash of the claims after the commit** (the entry `e` logged at `x` in the coherent claim
`(j, N, h)`, writing among its names only the free `bt`, which no other claim of `j` holds): one
of the claims before, on the tree itself (the rename dropped) or without `bt`. -/
theorem regionCrashed_cut {cl : List Claim} {n : Nat} {m' : Tree} {j : Ino} {N : NameSet}
    {h : NamesH} {x : Nat} {e : LogEntry} {c : Ents} {bt : GoString}
    (hr : RegionCrashed (replClaim (j, N, h) (j, N, h.log x e c) cl) n m')
    (hcl : (j, N, h) ∈ cl) (hcoh : ClaimCoh h j N) (hs : h.next ≤ e.start)
    (hbt : ∀ b, N.Mem b → e.op.Writes j b → b = bt) (hcur : h.cur !! bt = none)
    (hothers : ∀ c' ∈ cl, c' ≠ (j, N, h) → c'.1 = j → ¬ c'.2.1.Mem bt) :
    RegionCrashed cl n (treeDel m' j bt) ∨ RegionCrashed cl n m' := by
  obtain ⟨K, hK⟩ := (regionCrashed_iff _ _ _).1 hr
  by_cases hx : K x
  · obtain ⟨-, hK'⟩ := regionCrashedK_kept cl n m' K j N h x e c bt hK hx hcl hcoh hs hbt hcur
      hothers
    exact Or.inl ((regionCrashed_iff _ _ _).2 ⟨K, hK'⟩)
  · exact Or.inr ((regionCrashed_iff _ _ _).2 ⟨K, regionCrashedK_unlog cl n m' K j N h x e c hK hx⟩)

/-- A successful walk in the tree without `(j, bt)` is one in the tree. -/
theorem walk_treeDel {m : Tree} {j : Ino} {bt : GoString} :
    ∀ (cs : List GoString) (nd x : Node), walk (treeDel m j bt) nd cs = some x → walk m nd cs = some x
  | [], _, _, h => h
  | c :: cs, nd, x, h => by
    cases nd with
    | file _ => simp [walk] at h
    | dir j' =>
      simp only [walk] at h ⊢
      rw [treeDel_entry] at h
      by_cases hc : j' = j ∧ c = bt
      · rw [if_pos hc] at h; cases h
      · rw [if_neg hc] at h
        cases hm : m.entry j' c with
        | none => rw [hm] at h; cases h
        | some n' =>
          rw [hm] at h
          exact walk_treeDel cs n' x h

/-- **A successful lookup in the tree without `(j, bt)` is one in the tree.** -/
theorem lookupH_treeDel {R : Roots} {m : Tree} {j : Ino} {bt : GoString} {p : GoString} {x : Node}
    (h : lookupH R (treeDel m j bt, []) p = some x) : lookupH R (m, []) p = some x := by
  unfold lookupH OsState.lookup at *
  split at h
  · rename_i hc
    split
    · exact walk_treeDel _ _ _ h
    · rename_i hc'; exact absurd hc hc'
  · cases h

/-- **Another WAL's crash condition after the commit** (its directory and its area directory not
`j`; its alternative, if any, on the same names). -/
theorem crashOkA_cut_other {C : WalCodec} {Mr : WalMarshal} {d : WalDur} {lay : WalLay}
    {alt : Option WalLay} {cl : List Claim} {n : Nat} {j : Ino} {N : NameSet} {h : NamesH}
    {x : Nat} {e : LogEntry} {c : Ents} {bt : GoString}
    (hok : CrashOkA C Mr d lay alt cl n)
    (halt : ∀ lay0, alt = some lay0 → lay0.jr = lay.jr ∧ lay0.nm = lay.nm ∧ lay0.j = lay.j)
    (hlj : lay.j ≠ j) (hljr : lay.jr ≠ j)
    (hcl : (j, N, h) ∈ cl) (hcoh : ClaimCoh h j N) (hs : h.next ≤ e.start)
    (hbt : ∀ b, N.Mem b → e.op.Writes j b → b = bt) (hcur : h.cur !! bt = none)
    (hothers : ∀ c' ∈ cl, c' ≠ (j, N, h) → c'.1 = j → ¬ c'.2.1.Mem bt) :
    CrashOkA C Mr d lay alt (replClaim (j, N, h) (j, N, h.log x e c) cl) n := by
  intro m' fo hr hf hn hw
  rcases regionCrashed_cut hr hcl hcoh hs hbt hcur hothers with hr' | hr'
  · have hwi : walInos (entsOf (treeDel m' j bt) lay.j) = walInos (entsOf m' lay.j) := by
      rw [entsOf_treeDel_ne m' bt hlj]
    have hent : (treeDel m' j bt).entry lay.jr lay.nm = m'.entry lay.jr lay.nm := by
      rw [treeDel_entry]; simp [hljr]
    rcases hok (treeDel m' j bt) fo hr' hf (fun g hg hin => hn g hg (by rw [← hwi]; exact hin))
      (by rw [hwi]; exact hw) with hct | ⟨lay0, h0, hct⟩
    · exact Or.inl (crashTo_congr hent hwi hct)
    · obtain ⟨h1, h2, h3⟩ := halt lay0 h0
      refine Or.inr ⟨lay0, h0, crashTo_congr ?_ (by rw [h3]; exact hwi) hct⟩
      rw [h1, h2]; exact hent
  · exact hok m' fo hr' hf hn hw

end pure

end WalFs
end EtcdGrove
end Perennial

end

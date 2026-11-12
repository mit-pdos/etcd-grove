/-
`node.free` against the writer's freelist: corrected, proved forms of `Model/WOps`' stubs
`flView_canFree` and `flView_nodeFree`. For a node `n` of bucket `bl` cached at a position `pid`
of the logical tree (`resolve B pid = some n`), its page's slots are covered by `pid`'s extent, so
not pending (`flView`), not free and allocated before the view (`mvccView`); the ids are distinct
below `2^62`, so few enough: the page can be freed (`flView_canFree_pos`). Setting the node's page
id to `0` removes exactly that extent from the cover (`covU`: nothing else covers those slots),
and the free makes it pending (`flView_nodeFree_pos`, `flViewU` to `flViewU`).

The stubs take a live node (`n ∈ X.live`) in place of the position, which makes them false
without `wOK`/`liveReach`: a live node of `B.ns` that no position resolves to, whose page id is a
view page covered at another position (or pending), refutes both. A caller with `rblX` gets the
position from `node_pos` (`Rebalance/RblXSPos`).
-/
module

public import Proof.go_etcd_io.bbolt.Rebalance.RblXSFree
public import Proof.go_etcd_io.bbolt.Rebalance.RblXSRmT
public import Proof.go_etcd_io.bbolt.Write.DelBktFlvFl
public import Proof.go_etcd_io.bbolt.Rebalance.RblXSFl

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section flvn
variable [GooseExts]

/-- The extent of a position resolved to a node read from a page: the node's page's. -/
theorem posExtent_resolved (X : WX) (bl n : Loc) (B : BRec) (r : NRec) (pg : List w8) (pid : w64)
    (hB : X.t.bs !! bl = some B) (hres : resolve B pid = some n) (hr : B.ns !! n = some r)
    (hp0 : r.nv.pgid' ≠ W64 0) (hpg : X.v.pages !! r.nv.pgid'.toNat = some pg) :
    X.posExtent bl pid = some (r.nv.pgid', 1 + pageOverflow pg) := by
  unfold WX.posExtent
  simp only [hB, hres, hr, Option.map_some, Option.getD_some, if_neg hp0, hpg]

/-- **`node.free`'s `canFree`, from `flView`**: a node cached at a position of its bucket's
logical tree, read from a base page (covered by the position's extent, so not pending; a view
slot, so not free; allocated before the view, so not by the writer; the ids distinct below
`2^62`, so fewer than `2^62`). -/
theorem flView_canFree_pos (X : WX) (fl : FLPg) (txid : w64) (hv : flView X fl)
    (hx : pagesExt X.v.pages) (bl n : Loc) (B : BRec) (r : NRec) (pg : List w8) (pid : w64)
    (hB : X.t.bs !! bl = some B) (hr : B.ns !! n = some r) (hpos : pid ∈ X.positions bl)
    (hres : resolve B pid = some n) (hp0 : r.nv.pgid' ≠ W64 0)
    (hpg : X.v.pages !! r.nv.pgid'.toNat = some pg) (htx : X.v.txid < txid.toNat) :
    fl.canFree txid r.nv.pgid' (1 + pageOverflow pg) := by
  obtain ⟨hcov, hmv, hnd, hlt62⟩ := hv
  have hext0 := posExtent_resolved X bl n B r pg pid hB hres hr hp0 hpg
  have hext := hx _ pg hpg
  have hov : pageOverflow pg < 2 ^ 32 := by unfold pageOverflow; exact BitVec.isLt _
  have hcs0 : coversSlot X.v.pages r.nv.pgid'.toNat := ⟨_, pg, hpg, Nat.le_refl _, by omega⟩
  refine ⟨(hmv.2 _ hcs0).1, by omega, ?_, ?_, ?_⟩
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
    have hlc : lCovers X s := Or.inl ⟨bl, (r.nv.pgid', 1 + pageOverflow pg), by rw [hB]; simp,
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
      have : txid.toNat = 0 := by rw [← he]; rfl
      omega
    | some a =>
      simp only [Option.getD_some]
      have := hmv.1 _ pg hpg a (by rw [W64_ofInt_toNat]; exact ha)
      intro he; rw [he] at this; omega
  · have := nodup_len_le _ hnd hlt62
    omega

/-- **`flViewU` through `node.free`**: the node `n`, cached at the position `pid` of bucket `bl`,
gets page id `0`, and its page becomes pending for the writer. -/
theorem flView_nodeFree_pos (X : WX) (fl : FLPg) (txid : w64) (bl n : Loc) (B : BRec) (r : NRec)
    (pg : List w8) (pid : w64) (hv : flViewU X fl) (hB : X.t.bs !! bl = some B)
    (hr : B.ns !! n = some r) (hpos : pid ∈ X.positions bl) (hres : resolve B pid = some n)
    (hp0 : r.nv.pgid' ≠ W64 0) (hpg : X.v.pages !! r.nv.pgid'.toNat = some pg)
    (htx : X.v.txid < txid.toNat) :
    flViewU (X.setNode bl n { r with nv := { r.nv with pgid' := W64 0 } })
      (fl.freePages txid r.nv.pgid' (1 + pageOverflow pg)) := by
  obtain ⟨hfv, hu, hx, hal⟩ := hv
  have hcan := flView_canFree_pos X fl txid hfv hx bl n B r pg pid hB hr hpos hres hp0 hpg htx
  obtain ⟨E, hE⟩ : ∃ E, E = r.nv.pgid' := ⟨_, rfl⟩
  obtain ⟨N, hN⟩ : ∃ N, N = 1 + pageOverflow pg := ⟨_, rfl⟩
  rw [← hE, ← hN] at hcan ⊢
  have hE0 : E ≠ W64 0 := hE ▸ hp0
  obtain ⟨r', hr'⟩ : ∃ r' : NRec, r' = { r with nv := { r.nv with pgid' := W64 0 } } := ⟨_, rfl⟩
  rw [← hr']
  obtain ⟨B', hB'⟩ : ∃ B' : BRec, B' = { B with ns := B.ns.insert n r' } := ⟨_, rfl⟩
  have hX' : X.setNode bl n r' = X.setBkt bl B' := by
    simp only [WX.setNode, hB, hB']
  rw [hX']
  obtain ⟨X', hX'd⟩ : ∃ X', X' = X.setBkt bl B' := ⟨_, rfl⟩
  rw [← hX'd]
  have hext0 : X.posExtent bl pid = some (E, N) := by
    rw [hE, hN]; exact posExtent_resolved X bl n B r pg pid hB hres hr hp0 hpg
  have hvv : X'.v = X.v := by rw [hX'd]; rfl
  have hlook : X'.t.bs !! bl = some B' := by rw [hX'd, setBkt_look, if_pos rfl]
  have hres' : ∀ q, resolve B' q = resolve B q := fun q => by rw [hB']; rfl
  have hlt : ∀ c, ltree X' c = ltree X c := by
    intro c
    by_cases hc : c = bl
    · subst hc
      funext q
      unfold ltree
      rw [hlook, hB]
      simp only [hres', hvv]
      cases hq : resolve B q with
      | none => subst hB'; rfl
      | some l =>
        simp only
        by_cases hl : l = n
        · subst hl
          rw [show B'.ns = B.ns.insert l r' by rw [hB'], GMap.lookup_insert, hr, hr']
          rfl
        · rw [show B'.ns = B.ns.insert n r' by rw [hB'], GMap.lookup_insert_ne _ _ (Ne.symm hl)]
    · rw [hX'd]; exact setBkt_ltree_other X bl B' c hc
  have hfu : X'.fuel = X.fuel := by rw [hX'd]; exact setBkt_fuel X bl B B' hB
  have hrp : X'.rootPid = X.rootPid := by rw [hX'd]; exact setBkt_rootPid X bl B B' hB (by rw [hB'])
  have hposq : ∀ c, X'.positions c = X.positions c := by
    intro c; unfold WX.positions
    rw [hfu, hrp]
    exact lposF_congr _ _ c (fun q => by rw [hlt c]) _ _
  have hlv : ∀ c, X'.leaves c = X.leaves c := by
    intro c; unfold WX.leaves
    rw [hfu, hrp]
    exact lleaves_congr _ _ c (fun q => by rw [hlt c]) _ _
  have hrl : X'.rl = X.rl := by rw [hX'd]; rfl
  have hre : rootEnts X' = rootEnts X := by unfold rootEnts; rw [hrl, hlv]
  have hbk : bktLoc X' = bktLoc X := by
    funext m; unfold bktLoc; rw [hrl, hX'd, setBkt_look]
    split
    · rename_i h; rw [h, hB, hB']; rfl
    · rfl
  have hdom : ∀ c, (X'.t.bs !! c ≠ none) ↔ (X.t.bs !! c ≠ none) := by
    intro c; rw [hX'd, setBkt_look]; split
    · rename_i h; subst h; rw [hB]; simp
    · exact Iff.rfl
  -- the extents: unchanged but at the positions resolved to `n`, which have none
  have hpe : ∀ c q, X'.posExtent c q =
      if c = bl ∧ resolve B q = some n then none else X.posExtent c q := by
    intro c q
    by_cases hc : c = bl
    · subst hc
      unfold WX.posExtent
      rw [hlook, hB]
      simp only [hres', hvv]
      cases hq : resolve B q with
      | none => simp
      | some l =>
        by_cases hl : l = n
        · subst hl
          simp only [and_self, if_true]
          rw [show B'.ns = B.ns.insert l r' by rw [hB'], GMap.lookup_insert]
          simp [hr']
        · have : ¬ (some l = some n) := fun h => hl (Option.some.inj h)
          simp only [true_and, this, if_false]
          rw [show B'.ns = B.ns.insert n r' by rw [hB'], GMap.lookup_insert_ne _ _ (Ne.symm hl)]
    · rw [hX'd, setBkt_posExtent_other X bl B' c hc, if_neg (fun h => hc h.1)]
  have hEw : ∀ s, coverW X s (.pos bl pid) ↔ E.toNat ≤ s ∧ s < E.toNat + N := by
    intro s
    constructor
    · rintro ⟨-, -, e, he, h1, h2⟩
      rw [hext0] at he; cases he; exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨by rw [hB]; simp, hpos, (E, N), hext0, h1, h2⟩
  have hback : ∀ s c, coverW X' s c ↔ coverW X s c ∧ c ≠ .pos bl pid := by
    intro s c
    cases c with
    | pos c q =>
      show (X'.t.bs !! c ≠ none ∧ q ∈ X'.positions c ∧ ∃ e, X'.posExtent c q = some e ∧ _) ↔ _
      rw [hdom, hposq, hpe]
      by_cases hcq : c = bl ∧ resolve B q = some n
      · rw [if_pos hcq]
        simp only [reduceCtorEq, false_and, exists_false, and_false, false_iff]
        rintro ⟨hc, hne⟩
        obtain ⟨rfl, hq⟩ := hcq
        apply hne
        have hext1 : X.posExtent c q = some (E, N) := by
          rw [hE, hN]; exact posExtent_resolved X c n B r pg q hB hq hr hp0 hpg
        obtain ⟨-, -, e, he, h1, h2⟩ := id hc
        rw [hext1] at he; cases he
        have := hu s _ _ hc ((hEw s).2 ⟨h1, h2⟩)
        exact this
      · rw [if_neg hcq]
        constructor
        · intro h
          refine ⟨h, fun he => ?_⟩
          cases he
          exact hcq ⟨rfl, hres⟩
        · exact fun h => h.1
    | bkt m =>
      show (∃ v, (m, v) ∈ rootEnts X' ∧ bktLoc X' m = none ∧ bucketCovers X'.v.pages v s) ↔ _
      rw [hre, hbk, hvv]
      exact ⟨fun h => ⟨h, fun h' => by cases h'⟩, fun h => h.1⟩
  have hN64 : E.toNat + N < 2 ^ 64 := hcan.2.1
  have hcov : ∀ s, lCovers X' s ↔ lCovers X s ∧ ¬ (E.toNat ≤ s ∧ s < E.toNat + N) := by
    intro s
    rw [lCovers_iff, lCovers_iff]
    constructor
    · rintro ⟨c, hc⟩
      obtain ⟨hc0, hcE⟩ := (hback s c).1 hc
      exact ⟨⟨c, hc0⟩, fun hr => hcE (hu s c _ hc0 ((hEw s).2 hr))⟩
    · rintro ⟨⟨c, hc⟩, hr⟩
      refine ⟨c, (hback s c).2 ⟨hc, fun h => ?_⟩⟩
      subst h; exact hr ((hEw s).1 hc)
  have hpg' : X.v.pages !! E.toNat = some pg := hE ▸ hpg
  have hEx : E.toNat + N ≤ 2 ^ 62 := by rw [hN]; exact hx _ pg hpg'
  obtain ⟨hf1, hmv, hnd, h62⟩ := hfv
  have hcanA : fl.canFreeAll txid [(E, N)] := ⟨hcan, trivial⟩
  have hfa : fl.freeAll txid [(E, N)] = fl.freePages txid E N := rfl
  have hes : ∀ e ∈ [(E, N)], ∃ pg, X.v.pages !! e.1.toNat = some pg ∧ 1 + pageOverflow pg = e.2 := by
    intro e he; rw [List.mem_singleton] at he; subst he; exact ⟨pg, hpg', hN.symm⟩
  have hslt : ∀ s, coversSlot X.v.pages s → s < 2 ^ 64 := by
    rintro s ⟨id, pg1, h1, -, h2⟩
    have := hx id pg1 h1; omega
  have hmv' := Write.mvccView_freeAll X.v txid htx hslt [(E, N)] fl hcanA hal hes hmv
  have hids := Write.allIds_freeAll_ok txid [(E, N)] fl hcanA
    (by intro e he; rw [List.mem_singleton] at he; subst he; exact hEx) hnd h62
  rw [hfa] at hmv' hids
  refine ⟨⟨fun s hs => ?_, by rw [hvv]; exact hmv', hids.1, hids.2⟩, fun s c1 c2 h1 h2 => ?_,
    by rw [hvv]; exact hx, ?_⟩
  · rw [hvv] at hs
    rw [hcov, pendSlots_freePages fl txid E N hN64, hf1 s hs]
    exact not_or.symm
  · exact hu s c1 c2 ((hback s c1).1 h1).1 ((hback s c2).1 h2).1
  · exact Write.pendAligned_freePages fl txid E N hal

end flvn

end bbolt
end EtcdGrove
end Perennial

/-
`Bucket.spill` (U9p, `notes/bbolt-proof-plan.md`): **the slots owned at the start of the root
spill**. Before its loop over the cached child buckets, the root spill owns (`slotInv`, at the
spill's mark) the slots of the cached children's unspilled trees (`Dc`, each child's `uTree` slots
`D`, `bk_init`) and the root's own (`rootOwn X Dc`): every other base slot the logical trees cover
(`lCovers`: the root's positions, the uncached nested buckets' trees, the cached children without
a root node). Distinct: within a child's tree its pages are distinct (its nodes' pages by the page
cache, its page positions' subtrees by `posDisjoint`/`posNodeFree`), across the buckets by
`covU` (a child's slots are covered by its positions, `uTree_start_cov`), and `rootOwn` excludes
`Dc`. Owned: a covered base slot is below the committed mark, not free (`mvccView`) and not pending
(`flView`).
-/
module

public import Proof.go_etcd_io.bbolt.Spill.BktSlotCov

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

namespace Spill

section slot
variable [GooseExts]

open Classical in
/-- **The root's owned slots at the start of the spill**: the base slots covered by the logical
trees (`lCovers`) but not in the children's trees' slots `Dc`. -/
def rootOwn (X : WX) (Dc : List Nat) : List Nat :=
  (pagesSlots X.v.pages).filter fun s => decide (lCovers X s ∧ s ∉ Dc)

theorem mem_pagesSlots_cov {P : Pages} {s : Nat} : s ∈ pagesSlots P ↔ coversSlot P s := by
  simp only [pagesSlots, List.mem_flatMap, List.mem_range', coversSlot]
  constructor
  · rintro ⟨⟨id, pg⟩, hip, j, hj, rfl⟩
    exact ⟨id, pg, (GMap.mem_toList _ _ _).1 hip, by omega, by simp only at hj; omega⟩
  · rintro ⟨id, pg, hp, h1, h2⟩
    exact ⟨(id, pg), (GMap.mem_toList _ _ _).2 hp, s - id, by simp only; omega, by omega⟩

theorem pagesSlots_nodup' (P : Pages) (hd : pagesDisjoint P) : (pagesSlots P).Nodup := by
  unfold pagesSlots List.Nodup
  rw [List.pairwise_flatMap]
  refine ⟨fun a _ => List.nodup_range', ?_⟩
  have hk := GMap.toList_keys_nodup P
  rw [List.Nodup, List.pairwise_map] at hk
  refine List.Pairwise.imp_of_mem ?_ (List.Pairwise.and_mem.1 hk)
  intro a b ha hb hne x hx y hy hxy
  subst hxy
  simp only [List.mem_range'] at hx hy
  obtain ⟨i, hi, rfl⟩ := hx
  obtain ⟨j, hj, hij⟩ := hy
  rcases hd a.1 a.2 b.1 b.2 ((GMap.mem_toList _ _ _).1 ha) ((GMap.mem_toList _ _ _).1 hb)
    hne.2.2 with h | h <;> omega

/-- A witness covers. -/
theorem lCovers_of_coverW {X : WX} {s : Nat} {c : CovW} (hc : coverW X s c) : lCovers X s := by
  cases c with
  | pos bl pid =>
    obtain ⟨hne, hp, e, hx, h1, h2⟩ := hc
    exact Or.inl ⟨bl, e, hne, List.mem_filterMap.2 ⟨pid, hp, hx⟩, h1, h2⟩
  | bkt n =>
    obtain ⟨v, h1, h2, h3⟩ := hc
    exact Or.inr ⟨n, v, h1, h2, h3⟩

theorem mem_rootOwn {X : WX} {Dc : List Nat} {s : Nat} :
    s ∈ rootOwn X Dc ↔ coversSlot X.v.pages s ∧ lCovers X s ∧ s ∉ Dc := by
  unfold rootOwn
  rw [List.mem_filter, mem_pagesSlots_cov]
  simp only [decide_eq_true_eq]

/-- No buffer yet: the spill's page map is the view's. -/
theorem spP_clean {X : WX} (h : X.t.bufs = ∅) : spP X = X.v.pages := by
  apply GMap.ext
  intro x
  show (X.bufPages ∪ X.v.pages) !! x = X.v.pages !! x
  have hb : X.bufPages = ∅ := by
    unfold WX.bufPages; rw [h, GMap.toList_empty]; rfl
  rw [hb]
  exact GMap.lookup_union_r _ _ _ (GMap.lookup_empty x)

/-- **A cached child's unspilled tree at the start is covered by its positions** (`c` not the
root: its leaves plain). -/
theorem uTree_start_cov {X : WX} {fl : FLPg} (hpre : spillPre X fl) (hreach : liveReach X)
    (hv : flViewU X fl) {c : Loc} {Cc : BRec} (hc : X.t.bs !! c = some Cc) (hne : c ≠ X.rl)
    {h : Nat} {F D : List Nat} {N : List Loc} {E : List El}
    (hu : uTree X c (spP X) X.t.mv.pgid'.toNat Cc.bv.rootNode' none none h F D N E) :
    D.Nodup ∧ ∀ s ∈ D, coversSlot X.v.pages s ∧ ∃ pid, coverW X s (.pos c pid) := by
  have hok := hpre.1
  rw [spP_clean hok.1.2.1.2.1] at hu
  have hcl : bktClean X.v X.t.mv.pgid'.toNat c Cc := (hok.1.2.2.2.2.2 c Cc hc).1
  have hpd : pagesDisjoint X.v.pages := by
    obtain ⟨C', hC', hvC⟩ := hok.2.2.2.2.2.2.2
    rw [← hvC]; exact hC'.2.2.1
  have hnb : ∀ l r, Cc.ns !! l = some r → r.nv.isLeaf' = true → ∀ w ∈ r.ws,
      ¬ isBktFlag w.flags :=
    fun l r hr hl w hw hb => hne ((hok.1.2.1.2.2.1 c Cc hc l r hr hl w hw).1 hb)
  obtain ⟨hnd, hp⟩ := uTree_pieces hcl hc hpd hnb hu
  refine ⟨hnd, fun s hs => ⟨?_, Pc_cov hpre hreach hv hc hne (hp s hs)⟩⟩
  obtain ⟨p, pg, hpg, h1, h2, -⟩ := hp s hs
  exact ⟨p, pg, hpg, h1, h2⟩

/-- **A base slot covered other than by a child's position is the root's.** -/
theorem mem_rootOwn_of {X : WX} {fl : FLPg} (hpre : spillPre X fl) (hreach : liveReach X)
    (hv : flViewU X fl) (cs : List (Loc × List Nat))
    (hcs : ∀ c D, (c, D) ∈ cs → c ≠ X.rl ∧ ∃ Cc h F N E, X.t.bs !! c = some Cc ∧
      uTree X c (spP X) X.t.mv.pgid'.toNat Cc.bv.rootNode' none none h F D N E)
    {s : Nat} (hs : coversSlot X.v.pages s) {cw : CovW} (hcw : coverW X s cw)
    (hno : ∀ c D, (c, D) ∈ cs → ∀ pid, cw ≠ .pos c pid) :
    s ∈ rootOwn X (cs.flatMap Prod.snd) := by
  refine mem_rootOwn.2 ⟨hs, lCovers_of_coverW hcw, fun hm => ?_⟩
  obtain ⟨⟨c, D⟩, hcD, hsD⟩ := List.mem_flatMap.1 hm
  obtain ⟨hne, Cc, h, F, N, E, hc, hu⟩ := hcs c D hcD
  obtain ⟨pid, hpid⟩ := ((uTree_start_cov hpre hreach hv hc hne hu).2 s hsD).2
  exact hno c D hcD pid (hv.2.1 s _ _ hcw hpid)

/-- **The starting slot invariant of the root spill** (see the module doc): the children `cs`
(distinct, none the root), each with its unspilled tree's slots `D` (`bk_init`), and the root's
own slots. -/
theorem slotInv_start {X : WX} {fl : FLPg} {C : CommitSt} (hpre : spillPre X fl)
    (hreach : liveReach X) (hv : flViewU X fl) (hcok : treeOK C) (hcp : X.v.pages = C.pages)
    (hch : C.hwm ≤ X.t.mv.pgid'.toNat)
    (hids : ∀ id ∈ fl.allIds, id.toNat < X.t.mv.pgid'.toNat)
    (cs : List (Loc × List Nat)) (hnd : (cs.map Prod.fst).Nodup)
    (hcs : ∀ c D, (c, D) ∈ cs → c ≠ X.rl ∧ ∃ Cc h F N E, X.t.bs !! c = some Cc ∧
      uTree X c (spP X) X.t.mv.pgid'.toNat Cc.bv.rootNode' none none h F D N E) :
    slotInv fl X.t.mv.pgid'.toNat (rootOwn X (cs.flatMap Prod.snd) ++ cs.flatMap Prod.snd) := by
  have hcov : ∀ c D, (c, D) ∈ cs → D.Nodup ∧
      ∀ s ∈ D, coversSlot X.v.pages s ∧ ∃ pid, coverW X s (.pos c pid) := by
    intro c D hcD
    obtain ⟨hne, Cc, h, F, N, E, hc, hu⟩ := hcs c D hcD
    exact uTree_start_cov hpre hreach hv hc hne hu
  have hpd : pagesDisjoint X.v.pages := by rw [hcp]; exact hcok.2.2.1
  -- the children's slots are distinct
  have hDc : (cs.flatMap Prod.snd).Nodup := by
    refine nodup_flatMap_of' Prod.snd cs (fun a ha => (hcov a.1 a.2 ha).1) ?_
    intro i j a b x hij ha hb hxa hxb
    have hma := List.mem_of_getElem? ha
    have hmb := List.mem_of_getElem? hb
    obtain ⟨-, pa, hpa⟩ := (hcov a.1 a.2 hma).2 x hxa
    obtain ⟨-, pb, hpb⟩ := (hcov b.1 b.2 hmb).2 x hxb
    have e := hv.2.1 x _ _ hpa hpb
    simp only [CovW.pos.injEq] at e
    have hfa : (cs.map Prod.fst)[i]? = some a.1 := by simp [ha]
    have hfb : (cs.map Prod.fst)[j]? = some b.1 := by simp [hb]
    rw [e.1] at hfa
    have := nodup_idx' hnd hfa hfb
    omega
  -- every owned slot is a covered base slot
  have hall : ∀ s ∈ rootOwn X (cs.flatMap Prod.snd) ++ cs.flatMap Prod.snd,
      coversSlot X.v.pages s ∧ lCovers X s := by
    intro s hs
    rcases List.mem_append.1 hs with hs | hs
    · have := mem_rootOwn.1 hs; exact ⟨this.1, this.2.1⟩
    · obtain ⟨⟨c, D⟩, hcD, hsD⟩ := List.mem_flatMap.1 hs
      obtain ⟨hc1, pid, hpid⟩ := (hcov c D hcD).2 s hsD
      exact ⟨hc1, lCovers_of_coverW hpid⟩
  refine ⟨?_, ?_, hv.1.2.2.1, hids⟩
  · rw [List.nodup_append]
    refine ⟨(pagesSlots_nodup' _ hpd).sublist List.filter_sublist, hDc, ?_⟩
    intro x hx y hy hxy
    subst hxy
    exact (mem_rootOwn.1 hx).2.2 hy
  · intro s hs
    obtain ⟨⟨id, pg, hpg, h1, h2⟩, hl⟩ := hall s hs
    have hext := hv.2.2.1 id pg hpg
    have hcx : id + (1 + pageOverflow pg) ≤ C.hwm := hcok.2.2.2.1 id pg (by rw [← hcp]; exact hpg)
    have hcs' : coversSlot X.v.pages s := ⟨id, pg, hpg, h1, h2⟩
    refine ⟨by omega, by omega, ?_⟩
    unfold FLPg.allIds
    rw [List.mem_append]
    rintro (hf | hp)
    · exact (hv.1.2.1.2 s hcs').2.1 hf
    · have hnp := (hv.1.1 s hcs').1 hl
      apply hnp
      unfold pendSlots
      refine List.mem_map.2 ⟨_, hp, ?_⟩
      have : s < 2 ^ 64 := by omega
      simp only [BitVec.toNat_ofInt]
      omega

end slot

end Spill

end bbolt
end EtcdGrove
end Perennial

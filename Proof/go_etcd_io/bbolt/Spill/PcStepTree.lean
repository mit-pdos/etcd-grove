/-
`node.spill` after its children's loop (U9z3, `notes/bbolt-proof-plan.md`; pure): **the tree of a
written piece** (`pcTree`): the page `node.write` left for a piece (`pcPage`) over its entries'
subtrees (a leaf's nested buckets' values, a branch's finished subtrees, fixed after the children's
loop in an earlier page map that agrees on their pages) is an `sTree` within the piece's bounds,
its leaf elements the entries' (`pcEnts`), its first key the piece's. What `pcInv_stepX`'s new
piece needs (`Spill/NodeSpillTailStep`: `hft_new`, `hst_new`).
-/
module

public import Proof.go_etcd_io.bbolt.Spill.NodeSpillTailStepState
public import Proof.go_etcd_io.bbolt.Spill.NodeSpillTailPureEls
public import Proof.go_etcd_io.bbolt.Spill.STreeWrite
public import Proof.go_etcd_io.bbolt.Spill.PcStepBufs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

namespace Spill

section ptree
variable [GooseExts] [GoGlobalContext]

theorem pt_bkt_iff (f : w32) : isBktFlag f ↔ f.toNat % 2 = bucketLeafFlag := by
  unfold isBktFlag bucketLeafFlag
  have hk : (f &&& W32 1).toNat = f.toNat % 2 := by
    rw [BitVec.toNat_and]; show f.toNat &&& 1 = f.toNat % 2; rw [Nat.and_one_is_mod]
  constructor
  · intro h
    rcases Nat.mod_two_eq_zero_or_one f.toNat with h0 | h1
    · exact absurd (BitVec.eq_of_toNat_eq (by rw [hk, h0]; rfl)) h
    · exact h1
  · intro h he; have := congrArg BitVec.toNat he; rw [hk, h] at this; simp at this

theorem pt_lt_of_nlt_lt {a b c : List w8} (h1 : ¬ go.GoStringLt b a) (h2 : go.GoStringLt b c) :
    go.GoStringLt a c := by
  by_cases h : go.GoStringLt a b
  · exact go.goStringLt_trans h h2
  · rw [go.goStringLt_eq_of_not_lt h h1]; exact h2

/-- A tree's keys within a lower bound are within a weaker one. -/
theorem treeKeys_widenLo {P : Pages} {r : Nat} {lo hi : Option (List w8)}
    (h : treeKeys P r lo hi) : ∀ lo', (∀ k, keyGe lo k → keyGe lo' k) → treeKeys P r lo' hi := by
  induction h with
  | leaf root pg lo hi hp hf hk hb =>
    intro lo' hl
    exact treeKeys.leaf root pg lo' hi hp hf (fun i hi' => ⟨hl _ (hk i hi').1, (hk i hi').2⟩) hb
  | branch root pg lo hi kind hp hf h2 hk hc hch ih =>
    intro lo' hl
    refine treeKeys.branch root pg lo' hi kind hp hf h2
      (fun i hi' => ⟨hl _ (hk i hi').1, (hk i hi').2⟩) hc ?_
    intro i hi'
    by_cases h0 : i = 0
    · subst h0
      exact ih 0 hi' _ (fun k hk' => by
        unfold childLo at hk' ⊢; rw [if_pos rfl] at hk' ⊢; exact hl k hk')
    · have e : childLo lo' (branchKey pg) i = childLo lo (branchKey pg) i := by
        unfold childLo; rw [if_neg h0, if_neg h0]
      rw [e]; exact ih i hi' _ (fun _ h => h)

theorem sTree_widenLo {P : Pages} {hwm id : Nat} {lo lo' hi : Option (List w8)} {h : Nat}
    {S : List Nat} (hs : sTree P hwm id lo hi h S) (hl : ∀ k, keyGe lo k → keyGe lo' k) :
    sTree P hwm id lo' hi h S :=
  { hs with keys := treeKeys_widenLo hs.keys lo' hl }

theorem pt_mem_pgSlots {P : Pages} {S : List Nat} {x t : Nat} {pg : List w8} (hx : x ∈ S)
    (hp : P !! x = some pg) (h1 : x ≤ t) (h2 : t < x + (1 + pageOverflow pg)) :
    t ∈ pgSlots P S := by
  unfold pgSlots
  refine List.mem_flatMap.2 ⟨x, hx, ?_⟩
  rw [hp]; simp only [List.mem_range']; exact ⟨t - x, by omega, by omega⟩

theorem pt_extDisj {x y nx ny : Nat} {A B : List Nat} (hx : ∀ t, x ≤ t → t < x + nx → t ∈ A)
    (hy : ∀ t, y ≤ t → t < y + ny → t ∈ B) (hAB : ∀ t ∈ A, t ∉ B) (h1 : 0 < nx) (h2 : 0 < ny) :
    x + nx ≤ y ∨ y + ny ≤ x := by
  apply Classical.byContradiction; intro hc
  by_cases hxy : x ≤ y
  · exact hAB y (hx y hxy (by omega)) (hy y (Nat.le_refl _) (by omega))
  · exact hAB x (hx x (Nat.le_refl _) (by omega)) (hy x (by omega) (by omega))

theorem pt_disj_lt {f : Nat → List Nat} : ∀ n, ((List.range n).flatMap f).Nodup →
    ∀ i j, i < j → j < n → ∀ t ∈ f i, t ∉ f j := by
  intro n
  induction n with
  | zero => intro _ i j _ hj; omega
  | succ n ih =>
    intro hnd i j hij hj t ht ht'
    rw [List.range_succ, List.flatMap_append] at hnd
    have hnd' := List.nodup_append.1 hnd
    by_cases hjn : j < n
    · exact ih hnd'.1 i j hij hjn t ht ht'
    · have hjn' : j = n := by omega
      subst hjn'
      exact hnd'.2.2 t (List.mem_flatMap.2 ⟨i, List.mem_range.2 hij, ht⟩) t (by simpa using ht') rfl

theorem pt_disj {n : Nat} {f : Nat → List Nat} (hnd : ((List.range n).flatMap f).Nodup)
    {i j : Nat} (hi : i < n) (hj : j < n) (hij : i ≠ j) : ∀ t ∈ f i, t ∉ f j := by
  intro t ht ht'
  rcases Nat.lt_or_gt_of_ne hij with h | h
  · exact pt_disj_lt n hnd i j h hj t ht ht'
  · exact pt_disj_lt n hnd j i h hi t ht' ht

theorem pt_flatMap_congr {α β : Type} {l : List α} {f g : α → List β}
    (h : ∀ x ∈ l, f x = g x) : l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.flatMap_cons]
    rw [h a List.mem_cons_self, ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]

theorem pt_wKey {ws : List WEntry} {i : Nat} (h : i < ws.length) : wKey ws i = ws[i].key := by
  unfold wKey; rw [List.getElem?_eq_getElem h]; rfl

theorem pt_msKey (ws : List WEntry) : msKey (wsMs ws) = wKey ws := by
  funext j; unfold msKey wKey wsMs
  rw [List.getElem?_map, Option.map_map]; rfl

/-- **The tree of a written piece** (see the module doc): the page at `id` (`pcPage` of the
entries `ws0`, by data `ws`) in `P`, its entries' subtrees `Sb` agreeing with `P'` (below the
mark `hwm'`), owned (`pgSlots`, distinct) and outside the page's run: an `sTree` within
`[lo, hi)` of height `0` (a leaf) or `hc + 1` (a branch, over its entries' finished subtrees of
height `hc` within the entries' bounds), its leaf elements the entries', its first key the first
entry's (if any). -/
theorem pcTree {P P' : Pages} {hwm hwm' : Nat} {id : w64} {leaf : Bool} {ws ws0 : List WEntry}
    {count : Nat} {lo hi : Option (List w8)} {hc : Nat} {Sb : Nat → List Nat}
    {Eb : Nat → List El}
    (hpg : P !! id.toNat = some (pcPage id leaf ws0 count)) (hd0 : ws0.map wDat = ws.map wDat)
    (h2 : 2 ≤ id.toNat) (hext : id.toNat + count ≤ hwm) (hc0 : 0 < count)
    (hcnt : count - 1 < 2 ^ 32)
    (hbody : 16 + (pageBody true (wsMs ws)).length ≤ count * 4096)
    (hb : 16 + (pageBody true (wsMs ws)).length ≤ maxAllocSize)
    (hn : ws.length < 2 ^ 16)
    (hs : wsSorted ws) (hk0 : ∀ e ∈ ws, 0 < e.key.length) (hkin : ∀ e ∈ ws, keyIn lo hi e.key)
    (hhm : hwm' ≤ hwm)
    (hag : ∀ m < ws.length, ∀ y ∈ Sb m, P !! y = P' !! y)
    (hnd : ((List.range ws.length).flatMap fun m => pgSlots P' (Sb m)).Nodup)
    (hfr : ∀ m < ws.length, ∀ y ∈ pgSlots P' (Sb m), y < id.toNat ∨ id.toNat + count ≤ y)
    (hlf : leaf = true → ∀ m e, ws[m]? = some e →
      (isBktFlag e.flags → bvalS P' hwm' e.value (Sb m)) ∧ (¬ isBktFlag e.flags → Sb m = []))
    (hbr : leaf = false → 2 ≤ ws.length ∧ ∀ m e, ws[m]? = some e →
      fTree P' hwm' e.pgid.toNat e.key (childHi hi (wKey ws) ws.length m) hc (Sb m) (Eb m)) :
    sTree P hwm id.toNat lo hi (if leaf then 0 else hc + 1) (nodePages id.toNat ws.length Sb) ∧
    treeEls P id.toNat = (if leaf then ws.map wEl else (List.range ws.length).flatMap Eb) ∧
    (0 < ws.length → ∃ pg, P !! id.toNat = some pg ∧ 0 < pageCount pg ∧
      pageKey pg 0 = wKey ws 0) := by
  have hms : wsMs ws0 = wsMs ws := wsMs_congr' hd0
  have hml : (wsMs ws).length = ws.length := wsMs_length ws
  have hmk := pt_msKey ws
  have hb32 : 16 + (pageBody true (wsMs ws)).length < 2 ^ 32 := by
    unfold maxAllocSize at hb; omega
  have hn' : (wsMs ws).length < 2 ^ 16 := by rw [hml]; exact hn
  let ovf : w32 := W32 ((count - 1 : Nat) : Int)
  let tail : List w8 := List.replicate (count * 4096 - 16 - (pageBody leaf (wsMs ws)).length) (W8 0)
  have hpg' : P !! id.toNat = some (wPage id leaf (wsMs ws) ovf tail) := by
    rw [hpg]; unfold pcPage; rw [hms]
  have hov : ovf.toNat = count - 1 := by
    show (W32 ((count - 1 : Nat) : Int)).toNat = count - 1
    have := hcnt; word
  have hlen : (wPage id leaf (wsMs ws) ovf tail).length = (1 + ovf.toNat) * 4096 := by
    rw [wPage_length, List.length_replicate, hov]
    simp only [pageBody_length] at hbody ⊢
    omega
  have hext' : id.toNat + (1 + ovf.toNat) ≤ hwm := by rw [hov]; omega
  have hsrt : msSorted (wsMs ws) := by
    intro i j hij hj
    have hj' : j < ws.length := by rw [hml] at hj; exact hj
    have := hs i j hij hj'
    rw [pt_wKey (by omega), pt_wKey hj'] at this
    simpa [wsMs] using this
  have hk0' : ∀ m ∈ wsMs ws, 0 < m.key.length := by
    intro m hm
    unfold wsMs at hm
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hm
    exact hk0 e he
  have hkin' : ∀ m ∈ wsMs ws, keyIn lo hi m.key := by
    intro m hm
    unfold wsMs at hm
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hm
    exact hkin e he
  have hag' : ∀ m < ws.length, ∀ y ∈ Sb m, P' !! y = P !! y := fun m hm y hy => (hag m hm y hy).symm
  -- the subtrees' disjointness
  have hd : subsDisj P id.toNat (wPage id leaf (wsMs ws) ovf tail) (wsMs ws).length Sb := by
    rw [hml]
    refine ⟨fun i j hi hj hij x hx hx' => ?_, fun i hi hx => ?_, ?_, ?_⟩
    · exact pt_disj hnd hi hj hij x (mem_pgSlots_self hx) (mem_pgSlots_self hx')
    · rcases hfr i hi _ (mem_pgSlots_self hx) with h | h <;> omega
    · intro i j hi hj hij x hx y hy pgx pgy hpx hpy
      rw [hag i hi x hx] at hpx; rw [hag j hj y hy] at hpy
      exact pt_extDisj (fun t h1 h3 => pt_mem_pgSlots hx hpx h1 h3)
        (fun t h1 h3 => pt_mem_pgSlots hy hpy h1 h3) (pt_disj hnd hi hj hij) (by omega) (by omega)
    · intro i hi x hx pgx hpx
      rw [hag i hi x hx] at hpx
      unfold extDisj; rw [wPage_overflow, hov]
      rcases hfr i hi _ (mem_pgSlots_self hx) with h | h
      · right
        apply Classical.byContradiction; intro hc'
        rcases hfr i hi id.toNat (pt_mem_pgSlots hx hpx (by omega) (by omega)) with h' | h' <;>
          omega
      · left; omega
  have hcnt' := wPage_count (id := id) (leaf := leaf) (ovf := ovf) (tail := tail) hn'
  cases leaf with
  | true =>
    have hbv : ∀ i (hix : i < (wsMs ws).length), (wsMs ws)[i].flags.toNat % 2 = bucketLeafFlag →
        bvalS P hwm (wsMs ws)[i].value (Sb i) := by
      intro i hix hf
      have hix' : i < ws.length := by rw [hml] at hix; exact hix
      have h1 := (hlf rfl i ws[i] (List.getElem?_eq_getElem hix')).1
      simp only [wsMs, List.getElem_map] at hf ⊢
      exact bvalS_agree (hag i hix') hhm (h1 ((pt_bkt_iff _).2 hf))
    have hb0 : ∀ i (hix : i < (wsMs ws).length), (wsMs ws)[i].flags.toNat % 2 ≠ bucketLeafFlag →
        Sb i = [] := by
      intro i hix hf
      have hix' : i < ws.length := by rw [hml] at hix; exact hix
      simp only [wsMs, List.getElem_map] at hf
      exact (hlf rfl i ws[i] (List.getElem?_eq_getElem hix')).2 (fun h' => hf ((pt_bkt_iff _).1 h'))
    have Hs := sTree_wLeaf id (wsMs ws) ovf tail Sb hpg' h2 (by omega) hlen hn' hb hsrt hk0' hkin'
      hbv hb0 hd hext'
    rw [hml] at Hs
    refine ⟨Hs, ?_, fun hn0 => ⟨_, hpg', ?_, ?_⟩⟩
    · rw [treeEls_wLeaf hpg' hn' hb32]
      simp only [ite_true]; unfold wsMs; rw [List.map_map]; rfl
    · rw [hcnt', hml]; exact hn0
    · have hfl : pageFlags (wPage id true (wsMs ws) ovf tail) = leafPageFlag := by
        rw [wPage_flags]; rfl
      have hn0' : 0 < (wsMs ws).length := by rw [hml]; exact hn0
      unfold pageKey
      rw [if_pos (by rw [hfl]; rfl),
        (wPage_leaf (id := id) (ovf := ovf) (tail := tail) hn0' hb32).2.2.2.2.1, ← hmk, msKey_of hn0']
  | false =>
    obtain ⟨hn2, hbr⟩ := hbr rfl
    have hn2' : 2 ≤ (wsMs ws).length := by rw [hml]; exact hn2
    have hget : ∀ i (hix : i < (wsMs ws).length), ∃ hix' : i < ws.length,
        (wsMs ws)[i].pgid = ws[i].pgid ∧ (wsMs ws)[i].key = ws[i].key := by
      intro i hix
      exact ⟨by rw [hml] at hix; exact hix, by simp [wsMs], by simp [wsMs]⟩
    have hft : ∀ i (hix : i < ws.length), fTree P' hwm' ws[i].pgid.toNat ws[i].key
        (childHi hi (wKey ws) ws.length i) hc (Sb i) (Eb i) :=
      fun i hix => hbr i ws[i] (List.getElem?_eq_getElem hix)
    have hch : ∀ i (hix : i < (wsMs ws).length), sTree P hwm (wsMs ws)[i].pgid.toNat
        (childLo lo (msKey (wsMs ws)) i) (childHi hi (msKey (wsMs ws)) (wsMs ws).length i) hc
        (Sb i) := by
      intro i hix
      obtain ⟨hix', hp, -⟩ := hget i hix
      rw [hp, hmk, hml]
      have H := sTree_agree (hag i hix') hhm (hft i hix').1
      by_cases h0 : i = 0
      · subst h0
        unfold childLo; rw [if_pos rfl]
        refine sTree_widenLo H (fun k hk => ?_)
        have := (hkin ws[0] (List.getElem_mem _)).1
        intro l hl hlt
        exact this l hl (pt_lt_of_nlt_lt (hk _ rfl) hlt)
      · unfold childLo; rw [if_neg h0, pt_wKey hix']; exact H
    have hfirst : ∀ i (hix : i < (wsMs ws).length), ∃ cpg, P !! (wsMs ws)[i].pgid.toNat = some cpg ∧
        0 < pageCount cpg ∧ pageKey cpg 0 = (wsMs ws)[i].key := by
      intro i hix
      obtain ⟨hix', hp, hk⟩ := hget i hix
      rw [hp, hk]
      obtain ⟨cpg, hcp, h1, h3⟩ := (hft i hix').2.1
      refine ⟨cpg, ?_, h1, h3⟩
      rw [hag i hix' _ (sTree_root_mem (hft i hix').1)]; exact hcp
    have Hs := sTree_wBranch id (wsMs ws) ovf tail Sb hpg' h2 (by omega) hlen hn2' hn' hb hsrt hk0'
      hkin' hch hfirst hd hext'
    rw [hml] at Hs
    refine ⟨Hs, ?_, fun hn0 => ⟨_, hpg', ?_, ?_⟩⟩
    · rw [treeEls_wBranch hpg' hn' hb32 Sb _ _ _ hch hd.own]
      simp only [Bool.false_eq_true, ite_false]
      rw [← flatMap_range_getElem (wsMs ws), hml]
      refine pt_flatMap_congr fun i hi' => ?_
      have hix' := List.mem_range.1 hi'
      have hix : i < (wsMs ws).length := by rw [hml]; exact hix'
      rw [List.getElem?_eq_getElem hix, Option.map_some, Option.getD_some]
      obtain ⟨hx2, hp', -⟩ := hget i hix
      rw [hp', treeEls_agree (hft i hix').1 (hag i hix')]
      exact (hft i hix').2.2
    · rw [hcnt', hml]; exact hn0
    · have hfl : pageFlags (wPage id false (wsMs ws) ovf tail) = branchPageFlag := by
        rw [wPage_flags]; rfl
      have hn0' : 0 < (wsMs ws).length := by rw [hml]; exact hn0
      unfold pageKey
      rw [if_neg (by rw [hfl]; decide),
        (wPage_branch (id := id) (ovf := ovf) (tail := tail) hn0' hb32).2.2.2, ← hmk, msKey_of hn0']

end ptree

end Spill

end bbolt
end EtcdGrove
end Perennial

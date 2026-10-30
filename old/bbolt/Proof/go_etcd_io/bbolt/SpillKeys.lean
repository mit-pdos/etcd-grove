/-
A key's place in a bucket's logical tree, during `Commit`'s spill (`Bucket.spill`).

The logical tree's positions are page ids (`resolve`: a materialized node, else a page, as the
cursor sees them: `keysAt`, `kidsAt`). `tkp W B pid lo hi`: the tree from position `pid` has the
B+tree keys of `treeKeys`, over positions (nodes and pages alike). Then a key belongs to at most
one leaf: the descent by the key (`routePos`, what `kroute` follows) reaches every leaf holding
it (`routePos_of_has`), and is deterministic (`routePos_det`). `Bucket.spill` uses it to show
that `c.seek(name)` finds an opened child bucket's entry (no "misplaced bucket header" panic),
and to give each opened child's pages to the one position holding its entry.

`bktRanked B`: a child ranks below its parent (the node graph is a tree; the write path's
fact the spill needs, also for `dereference`'s `kidsTree`).
-/
module

public import Proof.go_etcd_io.bbolt.SpillDefs
public import Proof.go_etcd_io.bbolt.ShapeRoute
public import Proof.go_etcd_io.bbolt.PathFlags
public import Proof.go_etcd_io.bbolt.WriteCursorLemmas

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section keys
variable [ext : FfiSyntax]

/-- The nodes of `B` form a tree: a child ranks below its parent, the ranks bounded. -/
def bktRanked (B : BRec) : Prop :=
  ∃ (rk : Loc → Nat) (N : Nat), ∀ l r, B.ns !! l = some r → rk l ≤ N ∧
    (r.nv.parent' ≠ null → rk l < rk r.nv.parent')

/-- The key `i` of the keys `ks` (empty past the end). -/
def kAt (ks : List (List w8)) (i : Nat) : List w8 := ks.getD i []

/-- The tree from position `pid` has the keys of a B+tree with bounds `[lo, hi)`, over the
positions of `B` (see the module doc). -/
inductive tkp (W : WView) (B : BRec) : w64 → Option (List w8) → Option (List w8) → Prop
  | leaf (pid : w64) (ks : List (List w8)) (lo hi : Option (List w8)) :
      kidsAt W B pid = some (true, []) → keysAt W B pid = some ks → keysSorted ks →
      (∀ k ∈ ks, keyIn lo hi k) → tkp W B pid lo hi
  | branch (pid : w64) (ks : List (List w8)) (cs : List w64) (lo hi : Option (List w8)) :
      kidsAt W B pid = some (false, cs) → keysAt W B pid = some ks → keysSorted ks →
      cs.length = ks.length → (∀ k ∈ ks, keyIn lo hi k) →
      (∀ i c, cs[i]? = some c →
        tkp W B c (childLo lo (kAt ks) i) (childHi hi (kAt ks) ks.length i)) →
      tkp W B pid lo hi

/-- The position `pid'` is in the tree from `pid`. -/
inductive underPos (W : WView) (B : BRec) : w64 → w64 → Prop
  | self (pid : w64) : underPos W B pid pid
  | child (pid : w64) (cs : List w64) (i : Nat) (c pid' : w64) :
      kidsAt W B pid = some (false, cs) → cs[i]? = some c → underPos W B c pid' →
      underPos W B pid pid'

/-- The descent by the key `k` from `pid` ends at the leaf `e`. -/
inductive routePos (W : WView) (B : BRec) (k : List w8) : w64 → w64 → Prop
  | leaf (pid : w64) : kidsAt W B pid = some (true, []) → routePos W B k pid pid
  | step (pid : w64) (ks : List (List w8)) (cs : List w64) (i : Nat) (c e : w64) :
      keysAt W B pid = some ks → routes ks i k → kidsAt W B pid = some (false, cs) →
      cs[i]? = some c → routePos W B k c e → routePos W B k pid e

/-- The leaf position `pid` has the key `k`. -/
def leafHas (W : WView) (B : BRec) (pid : w64) (k : List w8) : Prop :=
  kidsAt W B pid = some (true, []) ∧ ∃ ks, keysAt W B pid = some ks ∧ k ∈ ks

/-- The stack elements `es` (`wpath`) from `pid` end at the position `e`. -/
inductive kpathEnd (W : WView) (B : BRec) : w64 → List elemRef → w64 → Prop
  | one (pid : w64) (r : elemRef) : kpathEnd W B pid [r] pid
  | cons (pid : w64) (r r2 : elemRef) (rs : List elemRef) (cs : List w64) (c e : w64) :
      kidsAt W B pid = some (false, cs) → cs[(sint.Z r.index').toNat]? = some c →
      kpathEnd W B c (r2 :: rs) e → kpathEnd W B pid (r :: r2 :: rs) e

/-! ### The order of keys -/

theorem notLt_trans {a b c : List w8} (h1 : ¬ go.GoStringLt a b) (h2 : ¬ go.GoStringLt b c) :
    ¬ go.GoStringLt a c := by
  intro hac
  rcases goStringLt_trichot_r a b with h | h | h
  · exact h1 h
  · subst h; exact h2 hac
  · exact h2 (goStringLt_trans h hac)

theorem lt_of_notLt_lt {a b c : List w8} (h1 : ¬ go.GoStringLt a b) (h2 : go.GoStringLt a c) :
    go.GoStringLt b c := by
  rcases goStringLt_trichot_r a b with h | h | h
  · exact absurd h h1
  · subst h; exact h2
  · exact goStringLt_trans h h2

/-- `routes` names one entry of sorted keys. -/
theorem routes_unique (ks : List (List w8)) (k : List w8) (hs : keysSorted ks) (i j : Nat)
    (hi : routes ks i k) (hj : routes ks j k) : i = j := by
  have key : ∀ i j, i < j → routes ks i k → routes ks j k → False := by
    intro i j hij hi hj
    obtain ⟨-, -, hin⟩ := hi
    obtain ⟨hjl, hj0, -⟩ := hj
    have hi1 : i + 1 < ks.length := by omega
    have hn := hin _ (List.getElem?_eq_getElem hi1)
    rcases hj0 with h0 | ⟨kj, hkj, hnl⟩
    · omega
    · by_cases e : i + 1 = j
      · subst e; rw [List.getElem?_eq_getElem hi1] at hkj; cases hkj; exact hnl hn
      · exact hnl (goStringLt_trans hn (hs (i + 1) j _ kj (by omega)
          (List.getElem?_eq_getElem hi1) hkj))
  rcases Nat.lt_trichotomy i j with h | h | h
  · exact (key i j h hi hj).elim
  · exact h
  · exact (key j i h hj hi).elim

theorem kAt_mem (ks : List (List w8)) (i : Nat) (h : i < ks.length) : kAt ks i ∈ ks := by
  unfold kAt; simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

theorem kAt_get (ks : List (List w8)) (i : Nat) (h : i < ks.length) :
    ks[i]? = some (kAt ks i) := by
  unfold kAt; simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

/-- A key in a child's bounds is in its parent's. -/
theorem keyIn_child (ks : List (List w8)) (lo hi : Option (List w8)) (k : List w8) (i : Nat)
    (hil : i < ks.length) (hb : ∀ k ∈ ks, keyIn lo hi k)
    (h : keyIn (childLo lo (kAt ks) i) (childHi hi (kAt ks) ks.length i) k) : keyIn lo hi k := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun l hl => ?_, fun hh hhh => ?_⟩
  · unfold childLo at h1
    split at h1
    · exact h1 l hl
    · exact notLt_trans (h1 _ rfl) ((hb _ (kAt_mem ks i hil)).1 l hl)
  · unfold childHi at h2
    split at h2
    · exact goStringLt_trans (h2 _ rfl) ((hb _ (kAt_mem ks _ (by omega))).2 hh hhh)
    · exact h2 hh hhh

/-- A key in a child's bounds is where the descent goes. -/
theorem routes_of_child (ks : List (List w8)) (lo hi : Option (List w8)) (k : List w8) (i : Nat)
    (hil : i < ks.length)
    (h : keyIn (childLo lo (kAt ks) i) (childHi hi (kAt ks) ks.length i) k) : routes ks i k := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨hil, ?_, fun kn hkn => ?_⟩
  · by_cases e : i = 0
    · exact Or.inl e
    · refine Or.inr ⟨kAt ks i, kAt_get ks i hil, ?_⟩
      unfold childLo at h1; rw [if_neg e] at h1; exact h1 _ rfl
  · have hl : i + 1 < ks.length := (List.getElem?_eq_some_iff.1 hkn).1
    rw [kAt_get ks _ hl] at hkn; cases hkn
    unfold childHi at h2; rw [if_pos hl] at h2; exact h2 _ rfl

theorem kidsAt_leaf_branch (W : WView) (B : BRec) (pid : w64) (cs cs' : List w64)
    (h1 : kidsAt W B pid = some (true, cs)) (h2 : kidsAt W B pid = some (false, cs')) : False := by
  rw [h1] at h2; cases h2

theorem kidsAt_leaf_nil (W : WView) (B : BRec) (pid : w64) (ks : List w64)
    (h : kidsAt W B pid = some (true, ks)) : ks = [] := by
  unfold kidsAt at h
  split at h
  · cases hn : B.ns !! _ with
    | none => rw [hn] at h; cases h
    | some r =>
      rw [hn] at h
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨h1, h2⟩ := h
      rw [h1] at h2; simp at h2; exact h2
  · cases hp : wpageAt W B pid with
    | none => rw [hp] at h; cases h
    | some lp =>
      rw [hp] at h
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨h1, h2⟩ := h
      have : pageFlags lp.2 = leafPageFlag := of_decide_eq_true h1
      rw [if_pos this] at h2; exact h2.symm

/-- The descent is deterministic. -/
theorem routePos_det (W : WView) (B : BRec) (k : List w8) (pid : w64) (lo hi : Option (List w8))
    (ht : tkp W B pid lo hi) (e1 e2 : w64) (h1 : routePos W B k pid e1)
    (h2 : routePos W B k pid e2) : e1 = e2 := by
  induction h1 generalizing lo hi e2 with
  | leaf pid hk =>
    cases h2 with
    | leaf _ _ => rfl
    | step _ _ _ _ _ _ _ _ hk' _ _ => exact (kidsAt_leaf_branch W B pid _ _ hk hk').elim
  | step pid ks cs i c e hks hr hk hc _ ih =>
    cases h2 with
    | leaf _ hk' => exact (kidsAt_leaf_branch W B pid _ _ hk' hk).elim
    | step _ ks' cs' j c' _ hks' hr' hk' hc' hrest =>
      rw [hks] at hks'; cases hks'
      rw [hk] at hk'; cases hk'
      cases ht with
      | leaf _ _ _ _ hk2 _ _ _ => exact (kidsAt_leaf_branch W B pid _ _ hk2 hk).elim
      | branch _ ks2 cs2 _ _ hk2 hks2 hs _ _ hch =>
        rw [hk] at hk2; cases hk2
        rw [hks] at hks2; cases hks2
        have := routes_unique ks k hs i j hr hr'
        subst this
        rw [hc] at hc'; cases hc'
        exact ih _ _ (hch i c hc) _ hrest

/-- A key in the tree from `pid` is in its bounds. -/
theorem keyIn_of_has (W : WView) (B : BRec) (k : List w8) (pid : w64) (lo hi : Option (List w8))
    (ht : tkp W B pid lo hi) (e : w64) (hu : underPos W B pid e) (hh : leafHas W B e k) :
    keyIn lo hi k := by
  induction hu generalizing lo hi with
  | self pid =>
    obtain ⟨hk, ks, hks, hm⟩ := hh
    cases ht with
    | leaf _ ks2 _ _ _ hks2 _ hb => rw [hks] at hks2; cases hks2; exact hb k hm
    | branch _ _ _ _ _ hk2 _ _ _ _ _ => exact (kidsAt_leaf_branch W B pid _ _ hk hk2).elim
  | child pid cs i c pid' hk hc _ ih =>
    cases ht with
    | leaf _ _ _ _ hk2 _ _ _ => exact (kidsAt_leaf_branch W B pid _ _ hk2 hk).elim
    | branch _ ks cs2 _ _ hk2 _ _ hlen hb hch =>
      rw [hk] at hk2; cases hk2
      have hil : i < ks.length := by rw [← hlen]; exact (List.getElem?_eq_some_iff.1 hc).1
      exact keyIn_child ks lo hi k i hil hb (ih _ _ (hch i c hc) hh)

/-- A leaf under `pid` holding `k` is where the descent by `k` ends. -/
theorem routePos_of_has (W : WView) (B : BRec) (k : List w8) (pid : w64) (lo hi : Option (List w8))
    (ht : tkp W B pid lo hi) (hk : keyIn lo hi k) (e : w64) (hu : underPos W B pid e)
    (hh : leafHas W B e k) : routePos W B k pid e := by
  induction hu generalizing lo hi with
  | self pid => exact routePos.leaf pid hh.1
  | child pid cs i c pid' hkd hc hu' ih =>
    cases ht with
    | leaf _ _ _ _ hk2 _ _ _ => exact (kidsAt_leaf_branch W B pid _ _ hk2 hkd).elim
    | branch _ ks cs2 _ _ hk2 hks _ hlen _ hch =>
      rw [hkd] at hk2; cases hk2
      have hil : i < ks.length := by rw [← hlen]; exact (List.getElem?_eq_some_iff.1 hc).1
      have hkc := keyIn_of_has W B k c _ _ (hch i c hc) pid' hu' hh
      exact routePos.step pid ks cs i c pid' hks (routes_of_child ks lo hi k i hil hkc) hkd hc
        (ih _ _ (hch i c hc) hkc hh)

/-- Two leaves holding the same key are one. -/
theorem leafHas_unique (W : WView) (B : BRec) (k : List w8) (pid : w64) (lo hi : Option (List w8))
    (ht : tkp W B pid lo hi) (e1 e2 : w64) (hu1 : underPos W B pid e1) (hu2 : underPos W B pid e2)
    (hh1 : leafHas W B e1 k) (hh2 : leafHas W B e2 k) : e1 = e2 :=
  routePos_det W B k pid lo hi ht e1 e2
    (routePos_of_has W B k pid lo hi ht (keyIn_of_has W B k pid lo hi ht e1 hu1 hh1) e1 hu1 hh1)
    (routePos_of_has W B k pid lo hi ht (keyIn_of_has W B k pid lo hi ht e2 hu2 hh2) e2 hu2 hh2)

/-- The cursor's descent by `k` (`kroute`, along a stack `wpath`) is `routePos`. -/
theorem routePos_of_kroute (W : WView) (B : BRec) (k : List w8) (pid : w64) (es : List elemRef)
    (hp : wpath W B pid es) (hr : kroute W B k pid es) (e : w64) (he : kpathEnd W B pid es e) :
    routePos W B k pid e := by
  induction he with
  | one pid r =>
    obtain ⟨-, -, ks, hk⟩ := hp
    rw [kidsAt_leaf_nil W B pid ks hk] at hk
    exact routePos.leaf pid hk
  | cons pid r r2 rs cs c e hk hc _ ih =>
    obtain ⟨-, -, cs', c', hk', hc', hp'⟩ := hp
    obtain ⟨ks, cs2, c2, hks, hro, hk2, hc2, hr'⟩ := hr
    rw [hk] at hk'; cases hk'
    rw [hk] at hk2; cases hk2
    rw [hc] at hc'; cases hc'
    rw [hc] at hc2; cases hc2
    exact routePos.step pid ks cs _ c e hks hro hk hc (ih hp' hr')

/-- A stack `wpath` ends somewhere. -/
theorem kpathEnd_of_wpath (W : WView) (B : BRec) (pid : w64) (es : List elemRef)
    (hp : wpath W B pid es) : ∃ e, kpathEnd W B pid es e := by
  induction es generalizing pid with
  | nil => exact hp.elim
  | cons r rest ih =>
    cases rest with
    | nil => exact ⟨pid, kpathEnd.one pid r⟩
    | cons r2 rs =>
      obtain ⟨-, -, cs, c, hk, hc, hp'⟩ := hp
      obtain ⟨e, he⟩ := ih c hp'
      exact ⟨e, kpathEnd.cons pid r r2 rs cs c e hk hc he⟩

/-! ### The positions' children and keys -/

theorem kidsAt_node (W : WView) (B : BRec) (pid : w64) (l : Loc) (r : NRec)
    (h : resolve B pid = some l) (hr : B.ns !! l = some r) :
    kidsAt W B pid = some (r.nv.isLeaf', if r.nv.isLeaf' then [] else r.ws.map WEntry.pgid) := by
  unfold kidsAt; rw [h]; simp [hr]

theorem keysAt_node (W : WView) (B : BRec) (pid : w64) (l : Loc) (r : NRec)
    (h : resolve B pid = some l) (hr : B.ns !! l = some r) :
    keysAt W B pid = some (r.ws.map WEntry.key) := by
  unfold keysAt; rw [h]; simp [hr]

theorem wpageAt_page (W : WView) (B : BRec) (pid : w64) (pg : List w8) (h0 : B.ib.root' ≠ W64 0)
    (hpg : W.pages !! uint.nat pid = some pg) :
    wpageAt W B pid = some (W.data +ₗ ((uint.nat pid * W.ps : Nat) : Int), pg) := by
  unfold wpageAt; rw [if_neg h0, hpg]; rfl

theorem kidsAt_page (W : WView) (B : BRec) (pid : w64) (p : Loc) (pg : List w8)
    (h : resolve B pid = none) (hp : wpageAt W B pid = some (p, pg)) :
    kidsAt W B pid = some (decide (pageFlags pg = leafPageFlag),
      if pageFlags pg = leafPageFlag then []
      else (List.range (pageCount pg)).map fun i => W64 (branchPgid pg i : Int)) := by
  unfold kidsAt; rw [h]; simp [hp]

theorem keysAt_page (W : WView) (B : BRec) (pid : w64) (p : Loc) (pg : List w8)
    (h : resolve B pid = none) (hp : wpageAt W B pid = some (p, pg)) :
    keysAt W B pid = some ((List.range (pageCount pg)).map (pageKey pg)) := by
  unfold keysAt; rw [h]; simp [hp]

theorem nat_w64_eq (x : Nat) (h : x < 2 ^ 64) : uint.nat (W64 (x : Int)) = x := by
  unfold uint.nat; word

theorem w64_nat_eq (x : w64) : W64 ((uint.nat x : Nat) : Int) = x := by
  unfold uint.nat; word

theorem childLo_congr (lo : Option (List w8)) (f g : Nat → List w8) (i : Nat)
    (h : f i = g i) : childLo lo f i = childLo lo g i := by
  unfold childLo; rw [h]

theorem childHi_congr (hi : Option (List w8)) (f g : Nat → List w8) (n i : Nat)
    (h : i + 1 < n → f (i + 1) = g (i + 1)) : childHi hi f n i = childHi hi g n i := by
  unfold childHi; split
  · rename_i hlt; rw [h hlt]
  · rfl

theorem kAt_range (n : Nat) (f : Nat → List w8) (j : Nat) (h : j < n) :
    kAt ((List.range n).map f) j = f j := by
  unfold kAt; simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range h]

theorem kAt_ws (ws : List WEntry) : kAt (ws.map WEntry.key) = wKey ws := by
  funext j; unfold kAt wKey; simp [List.getD_eq_getElem?_getD, List.getElem?_map]

theorem keysSorted_range (n : Nat) (f : Nat → List w8)
    (hs : ∀ i j, i < j → j < n → go.GoStringLt (f i) (f j)) :
    keysSorted ((List.range n).map f) :=
  keysSorted_fn (keysFn_range n f) hs

/-! ### The pages under a page position -/

/-- The pages under a page position (no node in its tree) have the keys of a B+tree. -/
theorem tkp_pages (W : WView) (B : BRec) (hwm : Nat) (hr0 : B.ib.root' ≠ W64 0) :
    ∀ x lo hi, treeKeys W.pages x lo hi → treeWF W.pages hwm x →
      (∀ d, treeHas W.pages x d → B.nm !! W64 (d : Int) = none) →
      ∀ pid, uint.nat pid = x → tkp W B pid lo hi := by
  intro x lo hi ht
  induction ht with
  | leaf root pg lo hi hpg hfl hkeys _ =>
    intro hwf hnm pid hpid
    subst hpid
    have hres : resolve B pid = none := by
      unfold resolve; rw [if_neg hr0]
      have := hnm _ (treeHas.root _ pg hpg); rwa [w64_nat_eq] at this
    have hwp := wpageAt_page W B pid pg hr0 hpg
    have hka := kidsAt_page W B pid _ pg hres hwp
    rw [if_pos hfl, decide_eq_true hfl] at hka
    have hks := keysAt_page W B pid _ pg hres hwp
    obtain ⟨-, -, -, hkd⟩ := treeWF_page _ _ _ pg hwf hpg
    have hpk : ∀ i, pageKey pg i = leafKey pg i := fun i => by unfold pageKey; rw [if_pos hfl]
    refine tkp.leaf pid _ lo hi hka hks (keysSorted_range _ _ ?_) ?_
    · intro i j hij hj
      rw [hpk, hpk]
      rcases hkd with ⟨-, hlw, -⟩ | ⟨hb, -, -⟩
      · exact hlw.2.2.2 i j hij hj
      · rw [hfl] at hb; exact absurd hb (by unfold branchPageFlag leafPageFlag; decide)
    · intro k hk
      obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hk
      rw [hpk]; exact hkeys i (List.mem_range.1 hi)
  | branch root pg lo hi kind hpg hfl h2 hkeys hfirst hch ih =>
    intro hwf hnm pid hpid
    subst hpid
    have hres : resolve B pid = none := by
      unfold resolve; rw [if_neg hr0]
      have := hnm _ (treeHas.root _ pg hpg); rwa [w64_nat_eq] at this
    have hnl : pageFlags pg ≠ leafPageFlag := by
      rw [hfl]; unfold branchPageFlag leafPageFlag; decide
    have hwp := wpageAt_page W B pid pg hr0 hpg
    have hka := kidsAt_page W B pid _ pg hres hwp
    rw [if_neg hnl, decide_eq_false hnl] at hka
    have hks := keysAt_page W B pid _ pg hres hwp
    obtain ⟨-, -, -, hkd⟩ := treeWF_page _ _ _ pg hwf hpg
    have hpk : ∀ i, pageKey pg i = branchKey pg i := fun i => by unfold pageKey; rw [if_neg hnl]
    obtain ⟨hbw, hcwf⟩ : branchWF pg pg.length hwm ∧
        ∀ i < pageCount pg, treeWF W.pages hwm (branchPgid pg i) := by
      rcases hkd with ⟨hl, -, -⟩ | ⟨-, hb, hc⟩
      · exact absurd hl hnl
      · exact ⟨hb, hc⟩
    refine tkp.branch pid _ _ lo hi hka hks (keysSorted_range _ _ ?_) (by simp) ?_ ?_
    · intro i j hij hj
      rw [hpk, hpk]; exact hbw.2.2.2.2 i j hij hj
    · intro k hk
      obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hk
      rw [hpk]; exact hkeys i (List.mem_range.1 hi)
    · intro i c hc
      rw [List.getElem?_map] at hc
      have hil : i < pageCount pg := by
        cases h : (List.range (pageCount pg))[i]? with
        | none => rw [h] at hc; cases hc
        | some _ => simpa using (List.getElem?_eq_some_iff.1 h).1
      rw [List.getElem?_range hil] at hc
      simp only [Option.map_some, Option.some.injEq] at hc
      subst hc
      have hlen : ((List.range (pageCount pg)).map (pageKey pg)).length = pageCount pg := by simp
      rw [hlen,
        childLo_congr lo _ (branchKey pg) i (by rw [kAt_range _ _ _ hil, hpk]),
        childHi_congr hi _ (branchKey pg) _ i (fun h => by rw [kAt_range _ _ _ h, hpk])]
      exact ih i hil (hcwf i hil)
        (fun d hd => hnm d (treeHas_child _ _ pg hpg hfl i hil d hd)) _
        (nat_w64_eq _ (by have := leAt_lt pg (elemOff i + 8) 8; unfold branchPgid; omega))

/-! ### Weakening the bounds -/

theorem tkp_weaken (W : WView) (B : BRec) :
    ∀ pid lo hi, tkp W B pid lo hi → ∀ lo' hi', (∀ k, keyGe lo k → keyGe lo' k) →
      (∀ k, keyLt k hi → keyLt k hi') → tkp W B pid lo' hi' := by
  intro pid lo hi ht
  induction ht with
  | leaf pid ks lo hi hk hks hs hb =>
    intro lo' hi' hl hh
    exact tkp.leaf pid ks lo' hi' hk hks hs (fun k hk => ⟨hl k (hb k hk).1, hh k (hb k hk).2⟩)
  | branch pid ks cs lo hi hk hks hs hlen hb _ ih =>
    intro lo' hi' hl hh
    refine tkp.branch pid ks cs lo' hi' hk hks hs hlen
      (fun k hk => ⟨hl k (hb k hk).1, hh k (hb k hk).2⟩) (fun i c hc => ih i c hc _ _ ?_ ?_)
    · intro k h; unfold childLo at h ⊢; split
      · rename_i e; rw [if_pos e] at h; exact hl k h
      · rename_i e; rw [if_neg e] at h; exact h
    · intro k h; unfold childHi at h ⊢; split
      · rename_i e; rw [if_pos e] at h; exact h
      · rename_i e; rw [if_neg e] at h; exact hh k h

theorem tkp_none (W : WView) (B : BRec) (pid : w64) (lo hi : Option (List w8))
    (h : tkp W B pid lo hi) : tkp W B pid none none :=
  tkp_weaken W B pid lo hi h none none (fun _ _ _ h => nomatch h) (fun _ _ _ h => nomatch h)

/-! ### The nodes -/

theorem resolve_ne_nullK (W : WView) (hwm : Nat) (bl : Loc) (B : BRec) (hc : bktClean W hwm bl B)
    (pid : w64) (l : Loc) (h : resolve B pid = some l) : l ≠ null := by
  unfold resolve at h
  split at h
  · split at h
    · cases h
    · cases h; assumption
  · exact (hc.2.2.2.2.1 pid l h).1

theorem pgid_idx_eq (ws : List WEntry) (h : (ws.map WEntry.pgid).Nodup) (i k : Nat)
    (w x : WEntry) (hi : ws[i]? = some w) (hk : ws[k]? = some x) (he : x.pgid = w.pgid) :
    k = i := by
  have h1 : (ws.map WEntry.pgid)[k]? = some x.pgid := by rw [List.getElem?_map, hk]; rfl
  have h2 : (ws.map WEntry.pgid)[i]? = some w.pgid := by rw [List.getElem?_map, hi]; rfl
  rw [he] at h1
  have hkl := (List.getElem?_eq_some_iff.1 h1).1
  have hil := (List.getElem?_eq_some_iff.1 h2).1
  exact (List.Nodup.getElem?_inj (by simpa using hkl) h).1 (h1.trans h2.symm)

theorem tkp_nodes (W : WView) (hwm : Nat) (bl : Loc) (B : BRec)
    (bnd : Loc → Option (List w8) × Option (List w8)) (hc : bktClean W hwm bl B)
    (hk : bktKeysB W B bnd) (rk : Loc → Nat)
    (hrk : ∀ l r, B.ns !! l = some r → r.nv.parent' ≠ null → rk l < rk r.nv.parent') :
    ∀ n l r pid, rk l < n → B.ns !! l = some r → resolve B pid = some l →
      tkp W B pid (bnd l).1 (bnd l).2 := by
  intro n
  induction n with
  | zero => intro l r pid h; omega
  | succ n ih =>
    intro l r pid hlt hr hres
    have hcl := hc.2.2.2.2.2.2.2.1 l r hr
    obtain ⟨hk1, -, -, hk4, -⟩ := hk.2.2 l r hr
    have hka := kidsAt_node W B pid l r hres hr
    have hks := keysAt_node W B pid l r hres hr
    have hsort : keysSorted (r.ws.map WEntry.key) := keysSorted_fn (keysFn_ws r.ws) hcl.2.2.1
    have hb : ∀ k ∈ r.ws.map WEntry.key, keyIn (bnd l).1 (bnd l).2 k := by
      intro k hk; obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hk; exact hk1 w hw
    cases hleaf : r.nv.isLeaf' with
    | true =>
      rw [hleaf] at hka; simp only [if_true] at hka
      exact tkp.leaf pid _ _ _ hka hks hsort hb
    | false =>
      rw [hleaf] at hka; simp only [Bool.false_eq_true, if_false] at hka
      have hr0 : B.ib.root' ≠ W64 0 := by
        intro h0; have := hc.2.2.2.2.2.2.1 h0 l r hr; rw [hleaf] at this; cases this
      obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hbr, -⟩ := hcl
      obtain ⟨-, hnd, hws⟩ := hbr hleaf
      obtain ⟨-, kind, hkind⟩ := hk4 hleaf
      have hlnn : l ≠ null := resolve_ne_nullK W hwm bl B hc pid l hres
      refine tkp.branch pid _ _ _ _ hka hks hsort (by simp) hb (fun i c hcs => ?_)
      rw [List.getElem?_map] at hcs
      cases hwi : r.ws[i]? with
      | none => rw [hwi] at hcs; cases hcs
      | some w =>
        rw [hwi] at hcs; simp only [Option.map_some, Option.some.injEq] at hcs
        subst hcs
        have hwmem := List.mem_of_getElem? hwi
        rw [kAt_ws, List.length_map]
        obtain ⟨-, hmat, hnone⟩ := hws w hwmem
        obtain ⟨hk4a, hk4b⟩ := hkind i w hwi
        cases hnm : B.nm !! w.pgid with
        | some y =>
          obtain ⟨ry, hry, hpar⟩ := hmat y hnm
          have hpy : ry.nv.parent' ≠ null := by rw [hpar]; exact hlnn
          have hrky := hrk y ry hry hpy
          rw [hpar] at hrky
          obtain ⟨-, -, hk3, -⟩ := hk.2.2 y ry hry
          obtain ⟨-, rp, i', w', hrp, hw', hpg, -, hbnd⟩ := hk3 hpy
          rw [hpar, hr] at hrp; cases hrp
          obtain ⟨-, ry', hry', hpg'⟩ := (hc.2.2.2.2.1 w.pgid y hnm)
          rw [hry] at hry'; cases hry'
          have hii : i' = i := pgid_idx_eq r.ws hnd i i' w w' hwi hw' (by rw [hpg, hpg'])
          subst hii
          rw [hpar] at hbnd
          have := ih y ry w.pgid (by omega) hry (by unfold resolve; rw [if_neg hr0]; exact hnm)
          rw [hbnd] at this
          exact this
        | none =>
          obtain ⟨pg, -, -, -, -, htk⟩ := hk4b hnm
          have hpos : pagePosAt B l i w.pgid := ⟨r, w, hr, hleaf, hwi, rfl, hnm⟩
          exact tkp_pages W B hwm hr0 _ _ _ htk (hnone hnm)
            (hc.2.2.2.2.2.2.2.2.2 l i w.pgid hpos) w.pgid rfl

/-- A clean, ranked bucket with its keys (`bktKeysB`) has the keys of a B+tree over its
positions, from its root. -/
theorem tkp_root (W : WView) (hwm : Nat) (bl : Loc) (B : BRec)
    (bnd : Loc → Option (List w8) × Option (List w8)) (hv : viewOK W) (hc : bktClean W hwm bl B)
    (hk : bktKeysB W B bnd) (hr : bktRanked B) :
    tkp W B B.ib.root' none none := by
  obtain ⟨rk, N, hrk⟩ := hr
  by_cases hrn : B.bv.rootNode' = null
  · by_cases h0 : B.ib.root' = W64 0
    · obtain ⟨hpg, -, hok⟩ := hc.1 h0 hrn
      have hres : resolve B B.ib.root' = none := by unfold resolve; rw [if_pos h0, if_pos hrn]
      have hwp : wpageAt W B B.ib.root' = some (B.bv.page', B.ipg) := by
        unfold wpageAt; rw [if_pos h0, if_pos h0]
      obtain ⟨-, hfl, hlw, -, -⟩ := hok
      have hka := kidsAt_page W B _ _ _ hres hwp
      rw [if_pos hfl, decide_eq_true hfl] at hka
      have hpk : ∀ i, pageKey B.ipg i = leafKey B.ipg i := fun i => by
        unfold pageKey; rw [if_pos hfl]
      refine tkp.leaf _ _ none none hka (keysAt_page W B _ _ _ hres hwp)
        (keysSorted_range _ _ (fun i j hij hj => by rw [hpk, hpk]; exact hlw.2.2.2 i j hij hj))
        (fun k _ => ⟨fun _ h => (nomatch h), fun _ h => (nomatch h)⟩)
    · have ht := hk.1 hrn h0
      obtain ⟨-, hwf⟩ := hc.2.1 h0
      have hnm : B.nm = ∅ := (hc.2.2.1 hrn).2
      exact tkp_pages W B hwm h0 _ _ _ ht (hwf hrn) (fun d _ => by rw [hnm]; rfl) _ rfl
  · have hnm := hc.2.2.2.1 hrn
    obtain ⟨-, r, hr, -⟩ := hc.2.2.2.2.1 _ _ hnm
    have hres : resolve B B.ib.root' = some B.bv.rootNode' := by
      unfold resolve; split
      · simp
      · exact hnm
    exact tkp_none W B _ _ _ (tkp_nodes W hwm bl B bnd hc hk rk (fun l r h hp => (hrk l r h).2 hp)
      (rk B.bv.rootNode' + 1) _ r _ (Nat.lt_succ_self _) hr hres)

/-! ### Where entries are -/

theorem uint_nat_lt' (x : w64) : uint.nat x < 2 ^ 64 := by unfold uint.nat; word

theorem underPos_trans (W : WView) (B : BRec) (a b c : w64) (h1 : underPos W B a b)
    (h2 : underPos W B b c) : underPos W B a c := by
  induction h1 with
  | self _ => exact h2
  | child pid cs i c' pid' hk hc _ ih => exact underPos.child pid cs i c' c hk hc (ih h2)

theorem underPos_snoc (W : WView) (B : BRec) (a b : w64) (cs : List w64) (i : Nat) (c : w64)
    (h : underPos W B a b) (hk : kidsAt W B b = some (false, cs)) (hc : cs[i]? = some c) :
    underPos W B a c :=
  underPos_trans W B a b c h (underPos.child b cs i c c hk hc (underPos.self c))

theorem ownHas_tree' (pages : GMap Nat (List w8)) (c p : Nat) (h : ownHas pages c p) :
    treeHas pages c p := by
  induction h with
  | root r pg hpg => exact treeHas.root r pg hpg
  | child r pg i id hpg hb hi _ ih => exact treeHas_child pages r pg hpg hb i hi id ih

/-- A node is under the root, up its parent chain. -/
theorem under_chain (W : WView) (hwm : Nat) (bl : Loc) (B : BRec) (hc : bktClean W hwm bl B)
    (rk : Loc → Nat) (N : Nat)
    (hrk : ∀ l r, B.ns !! l = some r → rk l ≤ N ∧ (r.nv.parent' ≠ null → rk l < rk r.nv.parent'))
    (h0 : B.ib.root' ≠ W64 0) :
    ∀ n l r, N - rk l < n → B.ns !! l = some r → underPos W B B.ib.root' r.nv.pgid' := by
  intro n
  induction n with
  | zero => intro l r h; omega
  | succ n ih =>
    intro l r hlt hr
    have hcl := hc.2.2.2.2.2.2.2.1 l r hr
    have hnml : B.nm !! r.nv.pgid' = some l := hcl.2.2.2.2.2.2.1
    by_cases hp : r.nv.parent' = null
    · have hroot := hcl.2.2.2.2.2.2.2.2.2.2.2.2.1 hp
      have hlnn : l ≠ null := (hc.2.2.2.2.1 _ _ hnml).1
      have hnm := hc.2.2.2.1 (by rw [hroot]; exact hlnn)
      rw [hroot] at hnm
      obtain ⟨-, r', hr', hpg⟩ := hc.2.2.2.2.1 _ _ hnm
      rw [hr] at hr'; cases hr'
      rw [hpg]; exact underPos.self _
    · obtain ⟨rp, hrp, hbr, -, w, hw, hwpg⟩ := hcl.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hp
      have hlt' := (hrk l r hr).2 hp
      have hle := (hrk _ rp hrp).1
      have hup := ih _ rp (by omega) hrp
      have hclp := hc.2.2.2.2.2.2.2.1 _ rp hrp
      have hresp : resolve B rp.nv.pgid' = some r.nv.parent' := by
        unfold resolve; rw [if_neg h0]; exact hclp.2.2.2.2.2.2.1
      have hka := kidsAt_node W B _ _ rp hresp hrp
      rw [hbr] at hka; simp only [Bool.false_eq_true, if_false] at hka
      obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hw
      refine underPos_snoc W B _ _ _ i _ hup hka ?_
      rw [List.getElem?_map, hi]; simp [hwpg]

/-- The pages under a position without nodes are under it. -/
theorem under_pages (W : WView) (B : BRec) (hr0 : B.ib.root' ≠ W64 0) :
    ∀ c p, ownHas W.pages c p → (∀ d, treeHas W.pages c d → B.nm !! W64 (d : Int) = none) →
      c < 2 ^ 64 → underPos W B (W64 (c : Int)) (W64 (p : Int)) := by
  intro c p h
  induction h with
  | root r pg hpg => intro _ _; exact underPos.self _
  | child r pg i id hpg hb hi _ ih =>
    intro hfree hr64
    have hres : resolve B (W64 (r : Int)) = none := by
      unfold resolve; rw [if_neg hr0]; exact hfree r (treeHas.root r pg hpg)
    have hwp := wpageAt_page W B (W64 (r : Int)) pg hr0 (by rw [nat_w64_eq r hr64]; exact hpg)
    have hnl : pageFlags pg ≠ leafPageFlag := by
      rw [hb]; unfold branchPageFlag leafPageFlag; decide
    have hka := kidsAt_page W B _ _ _ hres hwp
    rw [if_neg hnl, decide_eq_false hnl] at hka
    have h64 : branchPgid pg i < 2 ^ 64 := by
      have := leAt_lt pg (elemOff i + 8) 8; unfold branchPgid; omega
    refine underPos.child _ _ i _ _ hka (by simp [List.getElem?_range hi]) (ih ?_ h64)
    exact fun d hd => hfree d (treeHas_child _ _ pg hpg hb i hi d hd)

/-- The leaf position `e` has a nested bucket's entry with the key `k` and the value `v`. -/
def posKeyVal (W : WView) (B : BRec) (e : w64) (k v : List w8) : Prop :=
  (∀ l r, resolve B e = some l → B.ns !! l = some r →
    ∃ w ∈ r.ws, w.key = k ∧ w.value = v ∧ isBktFlag w.flags) ∧
  (resolve B e = none → ∃ lp i, wpageAt W B e = some lp ∧ i < pageCount lp.2 ∧
    leafKey lp.2 i = k ∧ leafValue lp.2 i = v ∧ leafFlags lp.2 i % 2 = bucketLeafFlag)

/-- An entry of a nested bucket of `B` (`entryIn`) is on a leaf position under the root, which
has its key. -/
theorem entryIn_posK (W : WView) (hwm : Nat) (bl : Loc) (B : BRec) (hv : viewOK W)
    (hc : bktClean W hwm bl B) (hr : bktRanked B) (k v : List w8) (h : entryIn W B k v) :
    ∃ e, underPos W B B.ib.root' e ∧ leafHas W B e k ∧ posKeyVal W B e k v := by
  obtain ⟨rk, N, hrk⟩ := hr
  rcases h with ⟨l, r, w, hr, hleaf, hw, hkey, hbkt, hval⟩ |
    ⟨c, p, pg, i, hpos, hown, hpg, hfl, hi, hkey, hbf, hval⟩
  · have hcl := hc.2.2.2.2.2.2.2.1 l r hr
    have hnml : B.nm !! r.nv.pgid' = some l := hcl.2.2.2.2.2.2.1
    have hlnn : l ≠ null := (hc.2.2.2.2.1 _ _ hnml).1
    have hres : resolve B r.nv.pgid' = some l := by
      unfold resolve
      split
      · rename_i h0
        have hpar : r.nv.parent' = null := by
          by_cases hp : r.nv.parent' = null
          · exact hp
          · obtain ⟨rp, hrp, hbr, -⟩ := hcl.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hp
            rw [hc.2.2.2.2.2.2.1 h0 _ rp hrp] at hbr; cases hbr
        have hroot := hcl.2.2.2.2.2.2.2.2.2.2.2.2.1 hpar
        rw [hroot, if_neg hlnn]
      · exact hnml
    have hu : underPos W B B.ib.root' r.nv.pgid' := by
      by_cases h0 : B.ib.root' = W64 0
      · rw [h0, hcl.2.2.2.2.2.2.2.1 h0]; exact underPos.self _
      · exact under_chain W hwm bl B hc rk N hrk h0 (N + 1) l r (by omega) hr
    refine ⟨r.nv.pgid', hu, ?_, ?_⟩
    · have hka := kidsAt_node W B _ l r hres hr
      rw [hleaf] at hka; simp only [if_true] at hka
      exact ⟨hka, _, keysAt_node W B _ l r hres hr, List.mem_map.2 ⟨w, hw, hkey⟩⟩
    · refine ⟨fun l' r' hl' hr' => ?_, fun h => by rw [hres] at h; cases h⟩
      rw [hres] at hl'; cases hl'; rw [hr] at hr'; cases hr'
      exact ⟨w, hw, hkey, hval, hbkt⟩
  · have hp64 : p < 2 ^ 64 := by
      have h1 := hv.2.2.2.1 p pg hpg
      have h2 := hv.2.1
      have : p ≤ p * W.ps := Nat.le_mul_of_pos_right p (by omega)
      omega
    -- the position: a page position under the root, its pages without nodes
    obtain ⟨hr0, hfree, hc64, huc⟩ : B.ib.root' ≠ W64 0 ∧
        (∀ d, treeHas W.pages c d → B.nm !! W64 (d : Int) = none) ∧ c < 2 ^ 64 ∧
        underPos W B B.ib.root' (W64 (c : Int)) := by
      rcases hpos with ⟨hrn, h0, rfl⟩ | ⟨l, j, ⟨rl, w, hrl, hbr, hwj, hpj, hnm⟩, hlt⟩
      · refine ⟨h0, fun d _ => by rw [(hc.2.2.1 hrn).2]; rfl, uint_nat_lt' _, ?_⟩
        rw [w64_nat_eq]; exact underPos.self _
      · have h0 : B.ib.root' ≠ W64 0 := by
          intro h0; rw [hc.2.2.2.2.2.2.1 h0 l rl hrl] at hbr; cases hbr
        refine ⟨h0, ?_, hlt, ?_⟩
        · have := hc.2.2.2.2.2.2.2.2.2 l j (W64 (c : Int)) ⟨rl, w, hrl, hbr, hwj, hpj, hnm⟩
          rwa [nat_w64_eq c hlt] at this
        · have hul := under_chain W hwm bl B hc rk N hrk h0 (N + 1) l rl (by omega) hrl
          have hcl := hc.2.2.2.2.2.2.2.1 l rl hrl
          have hresl : resolve B rl.nv.pgid' = some l := by
            unfold resolve; rw [if_neg h0]; exact hcl.2.2.2.2.2.2.1
          have hka := kidsAt_node W B _ l rl hresl hrl
          rw [hbr] at hka; simp only [Bool.false_eq_true, if_false] at hka
          refine underPos_snoc W B _ _ _ j _ hul hka ?_
          rw [List.getElem?_map, hwj]; simp [hpj]
    have hud := under_pages W B hr0 c p hown hfree hc64
    have hres : resolve B (W64 (p : Int)) = none := by
      unfold resolve; rw [if_neg hr0]
      exact hfree p (ownHas_tree' _ _ _ hown)
    have hwp := wpageAt_page W B (W64 (p : Int)) pg hr0 (by rw [nat_w64_eq p hp64]; exact hpg)
    refine ⟨W64 (p : Int), underPos_trans W B _ _ _ huc hud, ⟨?_, _, keysAt_page W B _ _ _ hres hwp, ?_⟩, ?_⟩
    · have hka := kidsAt_page W B _ _ _ hres hwp
      rw [if_pos hfl, decide_eq_true hfl] at hka; exact hka
    · refine List.mem_map.2 ⟨i, List.mem_range.2 hi, ?_⟩
      unfold pageKey; rw [if_pos hfl]; exact hkey
    · refine ⟨fun l' r' hl' _ => (by rw [hres] at hl'; cases hl'), fun _ => ⟨_, i, hwp, hi, hkey, hval, hbf⟩⟩

end keys

end bbolt
end EtcdGrove
end Perennial

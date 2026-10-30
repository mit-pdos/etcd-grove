/-
`Bucket.spill`'s pure and ghost lemmas.

- `bktRanked_of_keys`: a clean bucket with exact keys (`bktKeysB`) has its nodes a tree: a child's
  bounds are strictly inside its parent's (a branch has two entries), so ranking a node by the
  number of nodes whose bounds are strictly inside its own makes a child rank below its parent.
- `toks_split`: the tokens of the buckets reachable from `bl` are `bl`'s and, for each opened
  bucket, those reachable from it (the buckets' caches form a forest: `bmUnique`, `dep`).
-/
module

public import Spec.go_etcd_io.bbolt.Bucket__spill
public import Proof.go_etcd_io.bbolt.SpillReady

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section pure
variable [ext : FfiSyntax]

/-! ### A clean bucket with exact keys is ranked -/

/-- The bounds `c` are inside the bounds `p`. -/
def rkIn (c p : Option (List w8) × Option (List w8)) : Prop :=
  (∀ x, p.1 = some x → ∃ y, c.1 = some y ∧ ¬ go.GoStringLt y x) ∧
  (∀ y, p.2 = some y → ∃ x, c.2 = some x ∧ ¬ go.GoStringLt y x)

theorem rkIn_refl (c : Option (List w8) × Option (List w8)) : rkIn c c :=
  ⟨fun x h => ⟨x, h, goStringLt_irrefl_r x⟩, fun y h => ⟨y, h, goStringLt_irrefl_r y⟩⟩

theorem rkIn_trans (a b c : Option (List w8) × Option (List w8)) (h1 : rkIn a b) (h2 : rkIn b c) :
    rkIn a c := by
  refine ⟨fun x hx => ?_, fun y hy => ?_⟩
  · obtain ⟨y, hy, n1⟩ := h2.1 x hx
    obtain ⟨z, hz, n2⟩ := h1.1 y hy
    exact ⟨z, hz, notLt_trans n2 n1⟩
  · obtain ⟨x, hx, n1⟩ := h2.2 y hy
    obtain ⟨z, hz, n2⟩ := h1.2 x hx
    exact ⟨z, hz, notLt_trans n1 n2⟩

theorem rk_eq_of_notLt {a b : List w8} (h1 : ¬ go.GoStringLt a b) (h2 : ¬ go.GoStringLt b a) :
    a = b := by
  rcases goStringLt_trichot_r a b with h | h | h
  · exact absurd h h1
  · exact h
  · exact absurd h h2

theorem rkIn_antisymm (a b : Option (List w8) × Option (List w8)) (h1 : rkIn a b) (h2 : rkIn b a) :
    a = b := by
  obtain ⟨a1, a2⟩ := a
  obtain ⟨b1, b2⟩ := b
  obtain ⟨h11, h12⟩ := h1
  obtain ⟨h21, h22⟩ := h2
  simp only at h11 h12 h21 h22
  have e1 : a1 = b1 := by
    cases a1 with
    | none =>
      cases b1 with
      | none => rfl
      | some y => obtain ⟨_, h, _⟩ := h11 y rfl; cases h
    | some x =>
      obtain ⟨y, hy, n1⟩ := h21 x rfl
      subst hy
      obtain ⟨z, hz, n2⟩ := h11 y rfl
      cases hz
      rw [rk_eq_of_notLt n2 n1]
  have e2 : a2 = b2 := by
    cases a2 with
    | none =>
      cases b2 with
      | none => rfl
      | some y => obtain ⟨_, h, _⟩ := h12 y rfl; cases h
    | some x =>
      obtain ⟨y, hy, n1⟩ := h22 x rfl
      subst hy
      obtain ⟨z, hz, n2⟩ := h12 y rfl
      cases hz
      rw [rk_eq_of_notLt n1 n2]
  rw [e1, e2]

/-- Strictly inside. -/
def rkLt (c p : Option (List w8) × Option (List w8)) : Prop := rkIn c p ∧ c ≠ p

theorem rkLt_trans_in (a b c : Option (List w8) × Option (List w8)) (h1 : rkLt a b)
    (h2 : rkLt b c) : rkLt a c := by
  refine ⟨rkIn_trans a b c h1.1 h2.1, fun e => ?_⟩
  subst e
  exact h2.2 (rkIn_antisymm b a h2.1 h1.1)

theorem rk_wkey (ws : List WEntry) (i : Nat) (h : i < ws.length) : wKey ws i ∈ ws.map WEntry.key := by
  unfold wKey
  rw [List.getElem?_eq_getElem h]
  simp only [Option.map_some, Option.getD_some]
  exact List.mem_map.2 ⟨ws[i], List.getElem_mem h, rfl⟩

/-- A branch's child bounds are strictly inside its own. -/
theorem entryBnd_lt (b : Option (List w8) × Option (List w8)) (ws : List WEntry) (i : Nat)
    (hi : i < ws.length) (h2 : 2 ≤ ws.length) (hs : wsSorted ws)
    (hk : ∀ w ∈ ws, keyIn b.1 b.2 w.key) : rkLt (entryBnd b ws i) b := by
  have hkk : ∀ j, j < ws.length → keyIn b.1 b.2 (wKey ws j) := by
    intro j hj
    obtain ⟨w, hw, he⟩ := List.mem_map.1 (rk_wkey ws j hj)
    rw [← he]; exact hk w hw
  refine ⟨⟨fun x hx => ?_, fun y hy => ?_⟩, fun e => ?_⟩
  · unfold entryBnd childLo; simp only
    split
    · exact ⟨x, hx, goStringLt_irrefl_r x⟩
    · exact ⟨_, rfl, (hkk i hi).1 x hx⟩
  · unfold entryBnd childHi; simp only
    split
    · rename_i h
      exact ⟨_, rfl, goStringLt_asymm_b ((hkk (i + 1) h).2 y hy)⟩
    · exact ⟨y, hy, goStringLt_irrefl_r y⟩
  · by_cases h0 : i = 0
    · subst h0
      have e2 := congrArg Prod.snd e
      unfold entryBnd childHi at e2
      simp only [show 0 + 1 < ws.length from by omega, if_true] at e2
      have := (hkk 1 (by omega)).2 _ e2.symm
      exact goStringLt_irrefl_r _ this
    · have e1 := congrArg Prod.fst e
      unfold entryBnd childLo at e1
      simp only [h0, if_false] at e1
      have h0' := (hkk 0 (by omega)).1 _ e1.symm
      exact h0' (hs 0 i (by omega) hi)

theorem rk_filter_le {α : Type} (l : List α) (p q : α → Bool) (h : ∀ x ∈ l, p x → q x) :
    (l.filter p).length ≤ (l.filter q).length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have ih' := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    simp only [List.filter_cons]
    by_cases hp : p a
    · have hq := h a List.mem_cons_self hp
      simp [hp, hq]; omega
    · cases hq : q a <;> simp [hp, hq] <;> omega

theorem rk_filter_lt {α : Type} (l : List α) (p q : α → Bool) (h : ∀ x ∈ l, p x → q x)
    (x : α) (hx : x ∈ l) (hq : q x) (hp : ¬ p x) : (l.filter p).length < (l.filter q).length := by
  induction l with
  | nil => cases hx
  | cons a l ih =>
    have hle := rk_filter_le l p q (fun y hy => h y (List.mem_cons_of_mem _ hy))
    simp only [List.filter_cons]
    rcases List.mem_cons.1 hx with rfl | hx'
    · simp [hp, hq]; omega
    · have ih' := ih (fun y hy => h y (List.mem_cons_of_mem _ hy)) hx'
      by_cases hpa : p a
      · have hqa := h a List.mem_cons_self hpa
        simp [hpa, hqa]; omega
      · cases hqa : q a <;> simp [hpa, hqa] <;> omega

open Classical in
/-- A clean bucket with exact keys is ranked: a node ranks by how many nodes' bounds are
strictly inside its own (a child's are strictly inside its parent's). -/
theorem bktRanked_of_keys (W : WView) (hwm : Nat) (bl : Loc) (B : BRec)
    (bnd : Loc → Option (List w8) × Option (List w8)) (hc : bktClean W hwm bl B)
    (hk : bktKeysB W B bnd) : bktRanked B := by
  let L := B.ns.toList.map Prod.fst
  refine ⟨fun l => (L.filter (fun l' => decide (rkLt (bnd l') (bnd l)))).length, L.length,
    fun l r h => ⟨List.length_filter_le _ _, fun hp => ?_⟩⟩
  have hcl := hc.2.2.2.2.2.2.2.1
  obtain ⟨-, -, hpar, -⟩ := hk.2.2 l r h
  obtain ⟨-, rp, i, w, hrp, hw, -, -, hb⟩ := hpar hp
  obtain ⟨rp', hrp', hbr, -⟩ := (hcl l r h).2.2.2.2.2.2.2.2.2.2.2.2.2.1 hp
  rw [hrp] at hrp'; cases hrp'
  obtain ⟨hkp, -, -, hbrp, -⟩ := hk.2.2 _ rp hrp
  have hlt : rkLt (bnd l) (bnd r.nv.parent') := by
    rw [hb]
    exact entryBnd_lt _ rp.ws i (List.getElem?_eq_some_iff.1 hw).1 (hbrp hbr).1
      (hcl _ rp hrp).2.2.1 hkp
  have hmem : ∀ x, (B.ns !! x).isSome → x ∈ L := by
    intro x hx
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hx
    exact List.mem_map.2 ⟨(x, v), (GMap.mem_toList _ _ _).2 hv, rfl⟩
  apply rk_filter_lt L _ _ _ l (hmem l (by rw [h]; rfl))
  · simp only [decide_eq_true_eq]; exact hlt
  · simp only [decide_eq_true_eq]; exact fun h' => h'.2 rfl
  · intro x _ hx
    simp only [decide_eq_true_eq] at hx ⊢
    exact rkLt_trans_in _ _ _ hx hlt

theorem rs_trans (T : WTx) (a b c : Loc) (h1 : bktReach T a b) (h2 : bktReach T b c) :
    bktReach T a c := by
  induction h2 with
  | root => exact h1
  | child x X name y _ hX hn ih => exact bktReach.child x X name y ih hX hn

theorem rs_dep (T : WTx) (dep : Loc → Nat)
    (hdep : ∀ b C name c, T.bs !! b = some C → C.bm !! name = some c → dep c < dep b)
    (x d : Loc) (h : bktReach T x d) : dep d ≤ dep x := by
  induction h with
  | root => exact Nat.le_refl _
  | child p P name y _ hP hn ih => have := hdep p P name y hP hn; omega

/-- A path from `b` starts with one of its opened buckets. -/
theorem rs_first (T : WTx) (b : Loc) (B : BRec) (hB : T.bs !! b = some B) (d : Loc)
    (h : bktReach T b d) : d = b ∨ ∃ k c, B.bm !! k = some c ∧ bktReach T c d := by
  induction h with
  | root => exact Or.inl rfl
  | child x X name y hx hX hn ih =>
    right
    rcases ih with rfl | ⟨k, c, hc, hr⟩
    · rw [hB] at hX; cases hX; exact ⟨name, y, hn, bktReach.root⟩
    · exact ⟨k, c, hc, bktReach.child x X name y hr hX hn⟩

/-- Two buckets reaching one are comparable (the caches form a forest). -/
theorem rs_comparable (T : WTx) (hbu : bmUnique T) (x y d : Loc) (hx : bktReach T x d)
    (hy : bktReach T y d) : bktReach T x y ∨ bktReach T y x := by
  induction hx generalizing y with
  | root => exact Or.inr hy
  | child p P name z hpx hP hn ih =>
    cases hy with
    | root => exact Or.inl (bktReach.child p P name z hpx hP hn)
    | child p' P' name' _ hpy hP' hn' =>
      obtain ⟨rfl, -⟩ := hbu p P name p' P' name' z hP hn hP' hn'
      exact ih y hpy

theorem rs_nodup_flatMap {α β : Type} (f : α → List β) :
    ∀ (l : List α), (∀ x ∈ l, (f x).Nodup) →
      l.Pairwise (fun a b => ∀ y, y ∈ f a → y ∉ f b) → (l.flatMap f).Nodup
  | [], _, _ => List.nodup_nil
  | a :: l, h1, h2 => by
    rw [List.flatMap_cons, List.nodup_append]
    obtain ⟨h2a, h2l⟩ := List.pairwise_cons.1 h2
    refine ⟨h1 a List.mem_cons_self, rs_nodup_flatMap f l (fun x hx => h1 x (List.mem_cons_of_mem _ hx)) h2l, ?_⟩
    intro y hy z hz e
    subst e
    obtain ⟨x, hx, hyx⟩ := List.mem_flatMap.1 hz
    exact h2a x hx y hy hyx

open Classical in
/-- The buckets reachable from `b` (`Bs`), their caches a forest: `b` and, for each opened
bucket `c`, those reachable from `c`, disjointly. -/
theorem bs_reach_split (T : WTx) (dep : Loc → Nat)
    (hdep : ∀ b C name c, T.bs !! b = some C → C.bm !! name = some c → dep c < dep b)
    (hbu : bmUnique T) (b : Loc) (B : BRec) (hB : T.bs !! b = some B) (Bs : List Loc)
    (hnd : Bs.Nodup) (hBs : ∀ c, c ∈ Bs ↔ bktReach T b c) (keys : List GoString)
    (hk : ∀ k, k ∈ keys ↔ (B.bm !! k).isSome) (hkn : keys.Nodup) :
    Bs.Perm (b :: keys.flatMap (fun k => match B.bm !! k with
      | some c => Bs.filter (fun d => decide (bktReach T c d))
      | none => [])) := by
  -- the opened bucket `c` does not reach `b`
  have hnb : ∀ k c, B.bm !! k = some c → ¬ bktReach T c b := by
    intro k c hc hr
    have h1 := hdep b B k c hB hc
    have h2 := rs_dep T dep hdep c b hr
    omega
  have hmem : ∀ d k, d ∈ (match B.bm !! k with
      | some c => Bs.filter (fun d => decide (bktReach T c d))
      | none => []) ↔ ∃ c, B.bm !! k = some c ∧ d ∈ Bs ∧ bktReach T c d := by
    intro d k
    cases e : B.bm !! k with
    | none => simp
    | some c => simp [List.mem_filter]
  rw [List.perm_ext_iff_of_nodup hnd]
  · intro d
    rw [hBs d, List.mem_cons, List.mem_flatMap]
    constructor
    · intro h
      rcases rs_first T b B hB d h with rfl | ⟨k, c, hc, hr⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨k, (hk k).2 (by rw [hc]; rfl), (hmem d k).2 ⟨c, hc, (hBs d).2 h, hr⟩⟩
    · rintro (rfl | ⟨k, -, hd⟩)
      · exact bktReach.root
      · obtain ⟨c, hc, hdB, -⟩ := (hmem d k).1 hd
        exact (hBs d).1 hdB
  · rw [List.nodup_cons]
    refine ⟨fun h => ?_, ?_⟩
    · obtain ⟨k, -, hd⟩ := List.mem_flatMap.1 h
      obtain ⟨c, hc, -, hr⟩ := (hmem b k).1 hd
      exact hnb k c hc hr
    apply rs_nodup_flatMap
    · intro k _
      cases B.bm !! k with
      | none => exact List.nodup_nil
      | some c => exact hnd.sublist List.filter_sublist
    · refine hkn.imp ?_
      intro k1 k2 hne y hy1 hy2
      obtain ⟨c1, hc1, -, hr1⟩ := (hmem y k1).1 hy1
      obtain ⟨c2, hc2, -, hr2⟩ := (hmem y k2).1 hy2
      by_cases e : c1 = c2
      · subst e
        exact hne (hbu b B k1 b B k2 c1 hB hc1 hB hc2).2
      · -- one of them reaches the other, so it is not `b`'s child unless it reaches `b`
        have key : ∀ k k' c c', B.bm !! k = some c → B.bm !! k' = some c' → c ≠ c' →
            ¬ bktReach T c c' := by
          intro k k' c c' hc hc' hne' hr
          cases hr with
          | root => exact hne' rfl
          | child p P name _ hp hP hn =>
            obtain ⟨rfl, -⟩ := hbu p P name b B k' c' hP hn hB hc'
            exact hnb k c hc hp
        rcases rs_comparable T hbu c1 c2 y hr1 hr2 with h | h
        · exact key k1 k2 c1 c2 hc1 hc2 e h
        · exact key k2 k1 c2 c1 hc2 hc1 (Ne.symm e) h

theorem treeWF_page_some (P : GMap Nat (List w8)) (h x : Nat) (hw : treeWF P h x) :
    (P !! x).isSome := by
  cases hw with
  | page _ pg _ hpg _ _ => rw [hpg]; rfl

/-- What `node.spill` needs of a clean bucket's page ids (no page 0 in the view). -/
theorem clean_pgids (W : WView) (hwm : Nat) (bl : Loc) (B : BRec) (hc : bktClean W hwm bl B)
    (h0 : W.pages !! 0 = none) :
    (∀ l r, B.ns !! l = some r → r.nv.isLeaf' = false → r.nv.pgid' ≠ W64 0) ∧
    (∀ c l, B.nm !! c = some l → c = W64 0 ∨ (W.pages !! uint.nat c).isSome) ∧
    (∀ l r w, B.ns !! l = some r → r.nv.isLeaf' = false → w ∈ r.ws →
      (W.pages !! uint.nat w.pgid).isSome) := by
  have hcl := hc.2.2.2.2.2.2.2.1
  have hnz : ∀ l r, B.ns !! l = some r → r.nv.isLeaf' = false → B.ib.root' ≠ W64 0 := by
    intro l r h hb e
    rw [hc.2.2.2.2.2.2.1 e l r h] at hb; cases hb
  have hpg : ∀ l r, B.ns !! l = some r → B.ib.root' ≠ W64 0 →
      (W.pages !! uint.nat r.nv.pgid').isSome := by
    intro l r h hr
    exact treeWF_page_some _ _ _ ((hcl l r h).2.2.2.2.2.2.2.2.1 hr)
  refine ⟨fun l r h hb e => ?_, fun c l h => ?_, fun l r w h hb hw => ?_⟩
  · have := hpg l r h (hnz l r h hb)
    rw [e] at this
    have e0 : uint.nat (W64 0) = 0 := rfl
    rw [e0, h0] at this; cases this
  · obtain ⟨-, r, hr, hrp⟩ := hc.2.2.2.2.1 c l h
    by_cases e : B.ib.root' = W64 0
    · left; rw [← hrp]; exact (hcl l r hr).2.2.2.2.2.2.2.1 e
    · right; rw [← hrp]; exact hpg l r hr e
  · obtain ⟨-, -, hws⟩ := (hcl l r h).2.2.2.2.2.2.2.2.2.2.2.1 hb
    obtain ⟨-, hch, hnone⟩ := hws w hw
    cases hm : B.nm !! w.pgid with
    | none => exact treeWF_page_some _ _ _ (hnone hm)
    | some l' =>
      obtain ⟨-, r', hr', hrp'⟩ := hc.2.2.2.2.1 _ l' hm
      rw [← hrp']; exact hpg l' r' hr' (hnz l r h hb)

theorem bktReach_trans (T : WTx) (a b c : Loc) (h1 : bktReach T a b) (h2 : bktReach T b c) :
    bktReach T a c := by
  induction h2 with
  | root => exact h1
  | child x X name y _ hX hn ih => exact bktReach.child x X name y ih hX hn

theorem spillFrame_trans (T1 T2 T3 : WTx) (X Y : Loc → Prop) (h1 : spillFrame T1 T2 X)
    (h2 : spillFrame T2 T3 Y) (hY : ∀ c, Y c → X c) : spillFrame T1 T3 X := by
  obtain ⟨a1, b1, c1, d1, e1, f1⟩ := h1
  obtain ⟨a2, b2, c2, d2, e2, f2⟩ := h2
  refine ⟨fun c => (a1 c).trans (a2 c), b2.trans b1, Nat.le_trans c1 c2,
    GMap.map_subseteq_trans d1 d2, ?_, ?_⟩
  · rw [e2, e1]
  · intro c C C' hX hC hC'
    obtain ⟨C2, hC2⟩ := Option.isSome_iff_exists.1 ((a1 c).1 (by rw [hC]; rfl))
    have hY' : ¬ Y c := fun h => hX (hY c h)
    obtain ⟨s1, k1⟩ := f1 c C C2 hX hC hC2
    obtain ⟨s2, k2⟩ := f2 c C2 C' hY' hC2 hC'
    refine ⟨derefStarX_trans _ _ _ s1 s2, fun l r r' hr hr' => ?_⟩
    obtain ⟨r2, hr2⟩ := derefStarX_ns C2 C' s2 l r' hr'
    rw [k2 l r2 r' hr2 hr', k1 l r r2 hr hr2]

theorem spillFrame_refl (T : WTx) (X : Loc → Prop) : spillFrame T T X := by
  refine ⟨fun _ => Iff.rfl, rfl, Nat.le_refl _, GMap.map_subseteq_refl _, rfl, ?_⟩
  intro c C C' _ hC hC'
  rw [hC] at hC'; cases hC'
  refine ⟨Or.inl rfl, fun l r r' hr hr' => ?_⟩
  rw [hr] at hr'; cases hr'; rfl

theorem spillFrame_mono (T1 T2 : WTx) (X Y : Loc → Prop) (h : spillFrame T1 T2 X)
    (hXY : ∀ c, X c → Y c) : spillFrame T1 T2 Y := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨h1, h2, h3, h4, h5, fun c C C' hc => h6 c C C' (fun hx => hc (hXY c hx))⟩

/-- Only the bucket `bl` changed. -/
theorem spillFrame_upd (T : WTx) (bl : Loc) (B' : BRec) (X : Loc → Prop) (hX : X bl)
    (hbl : (T.bs !! bl).isSome) :
    spillFrame T { T with bs := <[bl := B']> T.bs } X := by
  refine ⟨fun c => ?_, rfl, Nat.le_refl _, GMap.map_subseteq_refl _, rfl, ?_⟩
  · by_cases e : bl = c
    · subst e; show _ ↔ ((<[bl := B']> T.bs) !! bl).isSome
      rw [GMap.lookup_insert]; simp [hbl]
    · show _ ↔ ((<[bl := B']> T.bs) !! c).isSome
      rw [GMap.lookup_insert_ne _ _ e]
  · intro c C C' hc hC hC'
    have e : bl ≠ c := fun h => hc (h ▸ hX)
    change (<[bl := B']> T.bs) !! c = some C' at hC'
    rw [GMap.lookup_insert_ne _ _ e, hC] at hC'
    cases hC'
    refine ⟨Or.inl rfl, fun l r r' hr hr' => ?_⟩
    rw [hr] at hr'; cases hr'; rfl

end pure

section facts2
variable [ext : FfiSyntax]

/-- The bucket with its root node `top` and its root page `pid`. -/
def setRootB (B : BRec) (top : Loc) (pid : w64) : BRec :=
  { B with bv := { B.bv with rootNode' := top }, ib := { B.ib with root' := pid } }

end facts2

section facts
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]

/-- Reachability over the buckets' caches depends only on them. -/
theorem bktReach_bm (T T' : WTx) (rl : Loc)
    (hbm : ∀ c C', T'.bs !! c = some C' → ∃ C, T.bs !! c = some C ∧ C'.bm = C.bm)
    (hdom : ∀ c, (T.bs !! c).isSome → (T'.bs !! c).isSome) :
    ∀ c, bktReach T rl c → bktReach T' rl c := by
  intro c h
  induction h with
  | root => exact bktReach.root
  | child x X name y _ hX hn ih =>
    obtain ⟨X', hX'⟩ := Option.isSome_iff_exists.1 (hdom x (by rw [hX]; rfl))
    obtain ⟨X0, hX0, hb⟩ := hbm x X' hX'
    rw [hX] at hX0; cases hX0
    exact bktReach.child x X' name y ih hX' (by rw [hb]; exact hn)

/-- The bucket's root set to the top of its spilled nodes (`b.rootNode = b.rootNode.root()`,
`SetRootPage`): the transaction's facts kept (its live nodes: the top alone). -/
theorem spillG_setRoot (W : WView) (txl : Loc) (txid : w64) (T : WTx) (ρ : DBState)
    (F : GMap Nat (List w8)) (bl : Loc) (B : BRec) (top : Loc) (rt : NRec) (pid : w64)
    (hg : spillG (hG := hG) W txl txid T ρ F) (hB : T.bs !! bl = some B)
    (ht : B.ns !! top = some rt) (hp : rt.nv.parent' = null) (hc : rt.cs = [])
    (hpid : rt.nv.pgid' = pid) (p : List Loc) (hup : upPath B.ns B.bv.rootNode' p top)
    (hrn : B.bv.rootNode' ≠ null) :
    spillG (hG := hG) W txl txid { T with bs := <[bl := setRootB B top pid]> T.bs } ρ F := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, hd⟩ := hg
  obtain ⟨d1, d2, ⟨dep, d3⟩, d4⟩ := hd
  have hlk : ∀ c, ({ T with bs := <[bl := setRootB B top pid]> T.bs } : WTx).bs !! c =
      if bl = c then some (setRootB B top pid) else T.bs !! c := by
    intro c
    show (<[bl := setRootB B top pid]> T.bs) !! c = _
    by_cases e : bl = c
    · subst e; rw [GMap.lookup_insert, if_pos rfl]
    · rw [GMap.lookup_insert_ne _ _ e, if_neg e]
  have hbm : ∀ c C', ({ T with bs := <[bl := setRootB B top pid]> T.bs } : WTx).bs !! c = some C' →
      ∃ C, T.bs !! c = some C ∧ C'.bm = C.bm := by
    intro c C' h
    rw [hlk] at h
    by_cases e : bl = c
    · rw [if_pos e] at h; cases h; subst e; exact ⟨B, hB, rfl⟩
    · rw [if_neg e] at h; exact ⟨C', h, rfl⟩
  have hdom : ∀ c, (T.bs !! c).isSome →
      (({ T with bs := <[bl := setRootB B top pid]> T.bs } : WTx).bs !! c).isSome := by
    intro c h
    rw [hlk]
    by_cases e : bl = c
    · rw [if_pos e]; rfl
    · rw [if_neg e]; exact h
  have hdom' : ∀ c, (({ T with bs := <[bl := setRootB B top pid]> T.bs } : WTx).bs !! c).isSome →
      (T.bs !! c).isSome := by
    intro c h
    rw [hlk] at h
    by_cases e : bl = c
    · subst e; rw [hB]; rfl
    · rw [if_neg e] at h; exact h
  refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, ?_, h11, h12, h13, hdom _ d1,
    fun c hc => bktReach_bm T _ _ hbm hdom c (d2 c (hdom' c hc)), ⟨dep, ?_⟩, ?_⟩
  · intro c C' h
    obtain ⟨C, hC, -⟩ := hbm c C' h
    rw [hlk] at h
    by_cases e : bl = c
    · rw [if_pos e] at h; cases h; subst e; rw [hB] at hC; cases hC
      show B.bv.tx' = txl; exact h10 _ _ hB
    · rw [if_neg e] at h; exact h10 c C' h
  · intro c C' name y h hn
    obtain ⟨C, hC, hb⟩ := hbm c C' h
    exact d3 c C name y hC (by rw [← hb]; exact hn)
  · intro c C' h
    obtain ⟨C, hC, hb⟩ := hbm c C' h
    obtain ⟨e1, e2⟩ := d4 c C hC
    refine ⟨?_, fun name y hn => hdom y (e2 name y (by rw [← hb]; exact hn))⟩
    rw [hlk] at h
    by_cases e : bl = c
    · rw [if_pos e] at h; cases h; subst e; rw [hB] at hC; cases hC
      right
      rcases e1 with e1 | ⟨S, ⟨p', top', hu', hnd', hk', -⟩, hok⟩
      · exact absurd e1 hrn
      obtain ⟨-, rfl⟩ := upPath_det B.ns hup hu'
      have htopS : top ∈ S := by cases hk' with | mk _ _ _ _ _ _ => exact List.mem_cons_self
      obtain ⟨r0, hr0, hok0⟩ := hok top htopS
      rw [ht] at hr0; cases hr0
      refine ⟨[top], ⟨[top], top, upPath.self (ns := (setRootB B top pid).ns) top rt ht hp, by simp, ?_, ?_⟩, ?_⟩
      · have := kidsTree.mk (ns := B.ns) top rt [] ht (by rw [hc]; exact List.Forall₂.nil)
          (by simp)
        simpa [setRootB] using this
      · intro l hl hn; exact absurd hl hn
      · intro l hl
        simp only [List.mem_singleton] at hl; subst hl
        exact ⟨rt, ht, hok0⟩
    · rw [if_neg e] at h; rw [h] at hC; cases hC; exact e1

end facts

end bbolt
end EtcdGrove
end Perennial

/-
net/http's Go 1.22 registration (`ServeMux.registerErr`'s steps) on literal path patterns
(`litPat`, `MuxTree.lean`).

* `routingIndexKey_safe`: the index's struct key compares by value (`go_eq_struct` over its two
  fields, `int` and `string`), so it is a safe map key.
* `wp_mapping_add`: `mapping.add` of a key not yet among the children.
-/
module

public import Net.Proof.net.http.MuxTree

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace net.http


/-! ### The tree while a pattern is added -/

section treePure
variable [GooseExts]

theorem lookupL_append_one {K V : Type} [DecidableEq K] (k k' : K) (v : V) :
    ∀ ps : List (K × V), map.lookupL k' (ps ++ [(k, v)]) =
      (match map.lookupL k' ps with | some x => some x | none => if k' = k then some v else none)
  | [] => by simp [map.lookupL]
  | p :: ps => by
    simp only [List.cons_append, map.lookupL]
    by_cases h : k' = p.1
    · simp [h]
    · simp only [h, ↓reduceIte]; exact lookupL_append_one k k' v ps

/-- What `TreeSt.ok` says of one node. -/
def nodeOk (S : TreeSt) (k : List Seg) (d : NodeSt) : Prop :=
  d.l ≠ null ∧
  (∀ s, s ≠ [] → map.lookupL s d.kids = (S.nodes !! (k ++ [.lit s])).map NodeSt.l) ∧
  d.empty = locOf (S.nodes !! (k ++ [.lit []])) ∧
  d.multi = locOf (S.nodes !! (k ++ [.multi])) ∧
  (∀ e ∈ S.pats, patKeys e.1 = k → d.pat = e.2.1 ∧ d.h = e.2.2) ∧
  ((∀ e ∈ S.pats, patKeys e.1 ≠ k) → d.pat = null ∧ d.h = interface.nil)

/-- `TreeSt.ok` while `addPattern` descends: the nodes it has made so far (on the way to the
current node `kc`) are prefixes of `kc`, every node's parent is a node. -/
def TreeSt.okP (root : Loc) (S : TreeSt) (kc : List Seg) : Prop :=
  (∃ d, S.nodes !! [] = some d ∧ d.l = root) ∧
  (∀ e ∈ S.pats, litPat e.1) ∧ (S.pats.map Prod.fst).Nodup ∧
  (∀ k, (S.nodes !! k).isSome → k = [] ∨ (∃ e ∈ S.pats, k <+: patKeys e.1) ∨ k <+: kc) ∧
  (∀ e ∈ S.pats, ∀ k, k <+: patKeys e.1 → (S.nodes !! k).isSome) ∧
  (S.nodes !! kc).isSome ∧
  (∀ k x, (S.nodes !! (k ++ [x])).isSome → (S.nodes !! k).isSome) ∧
  ∀ k d, S.nodes !! k = some d → nodeOk S k d

theorem isSome_of_prefix_aux (S : TreeSt) (hpar : ∀ k x, (S.nodes !! (k ++ [x])).isSome → (S.nodes !! k).isSome) :
    ∀ (n : Nat) (k k' : List Seg), k'.length = n → (S.nodes !! k').isSome → k <+: k' → (S.nodes !! k).isSome := by
  intro n
  induction n with
  | zero => intro k k' hl hk hp; rw [List.length_eq_zero_iff] at hl; subst hl
            rw [List.prefix_nil.mp hp]; exact hk
  | succ n ih =>
    intro k k' hl hk hp
    obtain ⟨k'', x, rfl⟩ : ∃ k'' x, k' = k'' ++ [x] := by
      have hne : k' ≠ [] := by intro h; subst h; simp at hl
      exact ⟨k'.dropLast, k'.getLast hne, (List.dropLast_concat_getLast hne).symm⟩
    rcases List.prefix_concat_iff.mp hp with h | h
    · subst h; exact hk
    · exact ih k k'' (by simp at hl; omega) (hpar _ _ hk) h

theorem TreeSt.ok_okP (root : Loc) (S : TreeSt) (hok : S.ok root) : S.okP root [] := by
  obtain ⟨hroot, hlit, hnd, hdom, hpre, hnodes⟩ := hok
  refine ⟨hroot, hlit, hnd, ?_, hpre, ?_, ?_, hnodes⟩
  · intro k hk
    rcases hdom k hk with h | h
    · exact .inl h
    · exact .inr (.inl h)
  · obtain ⟨d, hd, _⟩ := hroot; simp [hd]
  · intro k x hk
    rcases hdom _ hk with h | ⟨e, he, hp⟩
    · simp at h
    · exact hpre e he k ((List.prefix_append k [x]).trans hp)

theorem TreeSt.okP_mono (root : Loc) (S : TreeSt) (kc : List Seg) (x : Seg) (hok : S.okP root kc)
    (hx : (S.nodes !! (kc ++ [x])).isSome) : S.okP root (kc ++ [x]) := by
  obtain ⟨hroot, hlit, hnd, hdom, hpre, _, hpar, hnodes⟩ := hok
  refine ⟨hroot, hlit, hnd, ?_, hpre, hx, hpar, hnodes⟩
  intro k hk
  rcases hdom k hk with h | h | h
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr (h.trans (List.prefix_append kc [x])))


/-- A fresh node at `c` (`&routingNode{}`). -/
def freshNode (c : Loc) : NodeSt :=
  { l := c, pat := null, h := interface.nil, ms := ⟨slice.nil, map.nil, [], ∅⟩, kids := [],
    multi := null, empty := null }

/-- `d` with its link for the key `x` set to `c` (its children's state then `ms'`). -/
def linkUpd (d : NodeSt) (x : Seg) (c : Loc) (ms' : MapSt) : NodeSt :=
  match x with
  | .lit [] => { d with empty := c }
  | .lit s => { d with kids := d.kids ++ [(s, c)], ms := ms' }
  | .multi => { d with multi := c }

theorem linkUpd_l (d : NodeSt) (x : Seg) (c : Loc) (ms' : MapSt) : (linkUpd d x c ms').l = d.l := by
  unfold linkUpd; split <;> rfl

theorem linkUpd_pat (d : NodeSt) (x : Seg) (c : Loc) (ms' : MapSt) :
    (linkUpd d x c ms').pat = d.pat ∧ (linkUpd d x c ms').h = d.h := by
  unfold linkUpd; split <;> exact ⟨rfl, rfl⟩

theorem nodeOk_transfer (S S' : TreeSt) (k : List Seg) (d : NodeSt) (hpats : S'.pats = S.pats)
    (hmap : ∀ y, (S'.nodes !! (k ++ [y])).map NodeSt.l = (S.nodes !! (k ++ [y])).map NodeSt.l) :
    nodeOk S k d → nodeOk S' k d := by
  rintro ⟨h1, h2, h3, h4, h5, h6⟩
  refine ⟨h1, fun s hs => by rw [h2 s hs, hmap], ?_, ?_, by rw [hpats]; exact h5,
    by rw [hpats]; exact h6⟩
  · rw [h3]; unfold locOf; rw [hmap]
  · rw [h4]; unfold locOf; rw [hmap]

theorem append_single_ne {α : Type} (k : List α) (x : α) : k ≠ k ++ [x] := by
  intro h; have := congrArg List.length h; simp at this

theorem append_single_inj {α : Type} {k k' : List α} {x y : α} (h : k ++ [x] = k' ++ [y]) :
    k = k' ∧ x = y := by
  have := List.append_inj' h rfl; exact ⟨this.1, by simpa using this.2⟩

theorem TreeSt.okP_addNode (root : Loc) (S : TreeSt) (kc : List Seg) (x : Seg)
    (hok : S.okP root kc) (d : NodeSt) (hd : S.nodes !! kc = some d)
    (hfresh : S.nodes !! (kc ++ [x]) = none) (c : Loc) (hc : c ≠ null) (ms' : MapSt) :
    TreeSt.okP root { S with nodes := <[kc ++ [x] := freshNode c]> (<[kc := linkUpd d x c ms']> S.nodes) }
      (kc ++ [x]) := by
  obtain ⟨hroot, hlit, hnd, hdom, hpre, hkc, hpar, hnodes⟩ := hok
  have hne : kc ≠ kc ++ [x] := append_single_ne kc x
  have hlk : ∀ k, (<[kc ++ [x] := freshNode c]> (<[kc := linkUpd d x c ms']> S.nodes)) !! k =
      if kc ++ [x] = k then some (freshNode c) else if kc = k then some (linkUpd d x c ms')
      else S.nodes !! k := by
    intro k; simp only [GMap.lookup_insert_eq_iff]
  have hold : ∀ k, (S.nodes !! k).isSome →
      ((<[kc ++ [x] := freshNode c]> (<[kc := linkUpd d x c ms']> S.nodes)) !! k).isSome := by
    intro k hk; rw [hlk]
    by_cases a : kc ++ [x] = k <;> by_cases b : kc = k <;> simp [a, b, hk]
  have hbelow : ∀ y, S.nodes !! (kc ++ [x] ++ [y]) = none := by
    intro y
    cases h : S.nodes !! (kc ++ [x] ++ [y]) with
    | none => rfl
    | some _ => have := hpar (kc ++ [x]) y (by rw [h]; rfl); rw [hfresh] at this; simp at this
  refine ⟨?_, hlit, hnd, ?_, fun e he k hk => hold k (hpre e he k hk), by simp [hlk], ?_, ?_⟩
  · obtain ⟨d0, hd0, hl0⟩ := hroot
    by_cases h0 : kc = []
    · subst h0
      refine ⟨linkUpd d x c ms', ?_, by rw [linkUpd_l]; rw [hd] at hd0; cases hd0; exact hl0⟩
      rw [hlk]; simp
    · refine ⟨d0, ?_, hl0⟩
      rw [hlk]; simp [h0, hd0]
  · intro k hk
    rw [hlk] at hk
    by_cases h1 : kc ++ [x] = k
    · subst h1; exact .inr (.inr (List.prefix_refl _))
    by_cases h2 : kc = k
    · subst h2; exact .inr (.inr (List.prefix_append _ _))
    simp only [h1, h2, ↓reduceIte] at hk
    rcases hdom k hk with h | h | h
    · exact .inl h
    · exact .inr (.inl h)
    · exact .inr (.inr (h.trans (List.prefix_append kc [x])))
  · intro k y hk
    rw [hlk] at hk
    by_cases h1 : kc ++ [x] = k ++ [y]
    · obtain ⟨rfl, -⟩ := append_single_inj h1
      exact hold _ hkc
    by_cases h2 : kc = k ++ [y]
    · subst h2; exact hold _ (hpar k y (by rw [hd]; rfl))
    simp only [h1, h2, ↓reduceIte] at hk
    exact hold _ (hpar _ _ hk)
  · intro k d2 hk2
    rw [hlk] at hk2
    by_cases h1 : kc ++ [x] = k
    · subst h1
      simp only [↓reduceIte, Option.some.injEq] at hk2; subst hk2
      have hnone : ∀ y, (<[kc ++ [x] := freshNode c]> (<[kc := linkUpd d x c ms']> S.nodes)) !!
          (kc ++ [x] ++ [y]) = none := by
        intro y; rw [hlk]
        rw [if_neg (append_single_ne _ y), if_neg (fun h => by
          have := congrArg List.length h; simp at this), hbelow]
      refine ⟨hc, fun s _ => by rw [hnone]; rfl, by rw [hnone]; rfl, by rw [hnone]; rfl, ?_, fun _ => ⟨rfl, rfl⟩⟩
      intro e he hk
      have := hpre e he _ (by rw [hk]; exact List.prefix_refl _)
      rw [hfresh] at this; simp at this
    by_cases h2 : kc = k
    · subst h2
      simp only [h1, ↓reduceIte, Option.some.injEq] at hk2; subst hk2
      obtain ⟨n1, n2, n3, n4, n5, n6⟩ := hnodes kc d hd
      have hp := linkUpd_pat d x c ms'
      have hother : ∀ y, y ≠ x →
          (<[kc ++ [x] := freshNode c]> (<[kc := linkUpd d x c ms']> S.nodes)) !! (kc ++ [y]) =
            S.nodes !! (kc ++ [y]) := by
        intro y hy; rw [hlk, if_neg (fun h => hy (append_single_inj h).2.symm),
          if_neg (append_single_ne kc y)]
      refine ⟨by rw [linkUpd_l]; exact n1, ?_, ?_, ?_, ?_, ?_⟩
      · intro s hs
        by_cases hx : x = .lit s
        · subst hx
          obtain ⟨b, bs, rfl⟩ : ∃ b bs, s = b :: bs := List.exists_cons_of_ne_nil hs
          simp only [linkUpd]
          rw [lookupL_append_one, n2 _ hs, hfresh]
          simp [freshNode]
        · rw [hother _ (Ne.symm hx), ← n2 s hs]
          unfold linkUpd
          split
          · rfl
          · rename_i s' hs'
            rw [lookupL_append_one]
            cases map.lookupL s d.kids with
            | some _ => rfl
            | none => simp only; rw [if_neg (fun h => hx (by rw [h]))]
          · rfl
      · by_cases hx : x = .lit []
        · subst hx; simp [linkUpd, locOf, freshNode]
        · rw [hother _ (Ne.symm hx), ← n3]
          unfold linkUpd; split
          · exact absurd rfl hx
          · rfl
          · rfl
      · by_cases hx : x = .multi
        · subst hx; simp [linkUpd, locOf, freshNode]
        · rw [hother _ (Ne.symm hx), ← n4]
          unfold linkUpd; split
          · rfl
          · rfl
          · exact absurd rfl hx
      · intro e he hk; rw [hp.1, hp.2]; exact n5 e he hk
      · intro hall; rw [hp.1, hp.2]; exact n6 hall
    simp only [h1, h2, ↓reduceIte] at hk2
    refine nodeOk_transfer S
      { nodes := <[kc ++ [x] := freshNode c]> (<[kc := linkUpd d x c ms']> S.nodes), pats := S.pats }
      k d2 rfl ?_ (hnodes k d2 hk2)
    intro y
    rw [hlk, if_neg (fun h => h2 (append_single_inj h).1)]
    by_cases h3 : kc = k ++ [y]
    · rw [if_pos h3, ← h3, hd]; simp [linkUpd_l]
    · rw [if_neg h3]


/-- The path a list of segments spells (`pathSegs`' inverse). -/
def segsStr : List Seg → List w8
  | [] => []
  | .lit s :: r => W8 47 :: (s ++ segsStr r)
  | .multi :: r => W8 47 :: segsStr r

theorem segsStr_pathSegs : ∀ p, (p = [] ∨ p.head? = some (W8 47)) → segsStr (pathSegs p) = p := by
  apply pathSegs_ind
  · simp [pathSegs, segsStr]
  · rw [pathSegs_slash]; rfl
  · intro t ht ih
    rw [pathSegs_cons t ht]
    simp only [segsStr, ih]
    rw [List.takeWhile_append_dropWhile]

theorem patKeys_inj (p q : List w8) (hp : litPat p) (hq : litPat q) (h : patKeys p = patKeys q) :
    p = q := by
  have h' : pathSegs p = pathSegs q := by simpa [patKeys] using h
  rw [← segsStr_pathSegs p (.inr hp.1), ← segsStr_pathSegs q (.inr hq.1), h']

theorem patKeys_ne_nil (p : List w8) : patKeys p ≠ [] := by simp [patKeys]

/-- `d` holding the pattern `pp` and handler `h` (`set`). -/
def setPat (d : NodeSt) (pp : Loc) (h : GoInterface) : NodeSt := { d with pat := pp, h := h }


theorem pathSegs_multi_last : ∀ p, (p = [] ∨ p.head? = some (W8 47)) →
    ∀ l1 l2, pathSegs p = l1 ++ .multi :: l2 → l2 = [] := by
  apply pathSegs_ind
  · intro l1 l2 h; simp [pathSegs] at h
  · intro l1 l2 h; rw [pathSegs_slash] at h
    cases l1 with
    | nil => simp at h; exact h
    | cons a l1 => simp at h
  · intro t ht ih l1 l2 h
    rw [pathSegs_cons t ht] at h
    cases l1 with
    | nil => simp at h
    | cons a l1 => simp at h; exact ih l1 l2 h.2

/-- A key path ending in the multi wildcard that leads to a pattern is that pattern's. -/
theorem patKeys_multi_prefix (kc : List Seg) (q : List w8) (hq : litPat q)
    (h : kc ++ [.multi] <+: patKeys q) : patKeys q = kc ++ [.multi] := by
  obtain ⟨t, ht⟩ := h
  cases kc with
  | nil => simp [patKeys] at ht
  | cons a kc =>
    cases kc with
    | nil => simp [patKeys] at ht
    | cons b kc =>
      simp only [patKeys, List.cons_append, List.cons.injEq] at ht
      obtain ⟨ha, hb, ht⟩ := ht
      have := pathSegs_multi_last q (.inr hq.1) kc t (by rw [← ht]; simp)
      subst this; subst ha; subst hb; simp [patKeys, ← ht]

theorem TreeSt.okP_set (root : Loc) (S : TreeSt) (p : List w8) (pp : Loc) (h : GoInterface)
    (hok : S.okP root (patKeys p)) (hp : litPat p) (hnew : p ∉ S.pats.map Prod.fst)
    (d : NodeSt) (hd : S.nodes !! patKeys p = some d) :
    (d.pat = null ∧ d.h = interface.nil) ∧
    TreeSt.ok root (TreeSt.mk (<[patKeys p := setPat d pp h]> S.nodes) ((p, pp, h) :: S.pats)) := by
  obtain ⟨hroot, hlit, hnd, hdom, hpre, hkc, hpar, hnodes⟩ := hok
  have hother : ∀ e ∈ S.pats, patKeys e.1 ≠ patKeys p := by
    intro e he heq
    exact hnew (by rw [← patKeys_inj e.1 p (hlit e he) hp heq]; exact List.mem_map_of_mem he)
  obtain ⟨n1, n2, n3, n4, n5, n6⟩ := hnodes _ d hd
  refine ⟨n6 hother, ?_⟩
  have hlk : ∀ k, <[patKeys p := setPat d pp h]> S.nodes !! k =
      if patKeys p = k then some (setPat d pp h) else S.nodes !! k := by
    intro k; simp only [GMap.lookup_insert_eq_iff]
  have hmapl : ∀ k, (<[patKeys p := setPat d pp h]> S.nodes !! k).map NodeSt.l =
      (S.nodes !! k).map NodeSt.l := by
    intro k; rw [hlk]; by_cases hk : patKeys p = k
    · subst hk; rw [hd]; simp [setPat]
    · simp [hk]
  have hsome : ∀ k, (<[patKeys p := setPat d pp h]> S.nodes !! k).isSome =
      (S.nodes !! k).isSome := by
    intro k; have := congrArg Option.isSome (hmapl k); simpa using this
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨d0, hd0, hl0⟩ := hroot
    exact ⟨d0, by rw [hlk, if_neg (fun h => patKeys_ne_nil p h)]; exact hd0, hl0⟩
  · intro e he
    rcases List.mem_cons.mp he with rfl | he
    · exact hp
    · exact hlit e he
  · simp only [List.map_cons]; exact List.nodup_cons.mpr ⟨hnew, hnd⟩
  · intro k hk
    rw [hsome] at hk
    rcases hdom k hk with h0 | ⟨e, he, hpk⟩ | hpk
    · exact .inl h0
    · exact .inr ⟨e, List.mem_cons_of_mem _ he, hpk⟩
    · exact .inr ⟨(p, pp, h), List.mem_cons_self, hpk⟩
  · intro e he k hk
    rw [hsome]
    rcases List.mem_cons.mp he with rfl | he
    · exact isSome_of_prefix_aux S hpar _ k _ rfl hkc hk
    · exact hpre e he k hk
  · intro k d2 hk2
    rw [hlk] at hk2
    have hch : ∀ y, (<[patKeys p := setPat d pp h]> S.nodes !! (k ++ [y])).map
        NodeSt.l = (S.nodes !! (k ++ [y])).map NodeSt.l := fun y => hmapl _
    have hloc : ∀ y, locOf (<[patKeys p := setPat d pp h]> S.nodes !! (k ++ [y])) =
        locOf (S.nodes !! (k ++ [y])) := fun y => by unfold locOf; rw [hch]
    by_cases hk : patKeys p = k
    · subst hk
      simp only [↓reduceIte, Option.some.injEq] at hk2; subst hk2
      refine ⟨n1, fun s hs => by rw [hch]; exact n2 s hs, by rw [hloc]; exact n3,
        by rw [hloc]; exact n4, ?_, ?_⟩
      · intro e he hek
        rcases List.mem_cons.mp he with rfl | he
        · exact ⟨rfl, rfl⟩
        · exact absurd hek (hother e he)
      · intro hall; exact absurd rfl (hall _ List.mem_cons_self)
    · simp only [hk, ↓reduceIte] at hk2
      obtain ⟨m1, m2, m3, m4, m5, m6⟩ := hnodes k d2 hk2
      refine ⟨m1, fun s hs => by rw [m2 s hs, hch], by rw [hloc]; exact m3, by rw [hloc]; exact m4,
        ?_, ?_⟩
      · intro e he hek
        rcases List.mem_cons.mp he with rfl | he
        · exact absurd hek hk
        · exact m5 e he hek
      · intro hall; exact m6 (fun e he => hall e (List.mem_cons_of_mem _ he))

end treePure

section wp
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics] [package_sem' : net.http.Assumptions]

instance routingIndexKey.decEq : DecidableEq net.http.routingIndexKey := fun a b =>
  decidable_of_iff (a.pos' = b.pos' ∧ a.s' = b.s') (by cases a; cases b; simp)

instance routingIndexKey_safe (k : net.http.routingIndexKey) :
    SafeMapKey (GF := GF) (keys := mapKeys_all _) net.http.routingIndexKey.ty k where
  key_ok := trivial
  wp_go_eq_map_key k' _ s E Φ := by
    iintro HΦ
    wp_auto
    by_cases hp : k.pos' = k'.pos'
    · rw [decide_eq_true hp]
      wp_auto
      have : decide (k = k') = decide (k.s' = k'.s') := by
        cases k; cases k'; simp at hp ⊢; simp [hp]
      rw [this]
      iapply HΦ
    · rw [decide_eq_false hp]
      wp_auto
      have : decide (k = k') = false := decide_eq_false (fun h => hp (by rw [h]))
      rw [this]
      iapply HΦ

theorem kids_append_nodup (kids : List (GoString × Loc)) (k : GoString) (v : Loc)
    (hnd : (kids.map Prod.fst).Nodup) (hk : map.lookupL k kids = none) :
    ((kids ++ [(k, v)]).map Prod.fst).Nodup := by
  rw [List.map_append, List.nodup_append]
  refine ⟨hnd, by simp, ?_⟩
  intro a ha b hb; simp at hb; subst hb
  intro hab; subst hab
  exact (map.lookupL_eq_none_iff _ _).mp hk ha

theorem entPairs_take_succ (es : List (net.http.entry GoString Loc)) (i : Nat)
    (x : net.http.entry GoString Loc) (hx : es[i]? = some x) :
    entPairs (es.take (i + 1)) = entPairs (es.take i) ++ [(x.key', x.value')] := by
  have hi : i < es.length := (List.getElem?_eq_some_iff.mp hx).1
  rw [List.take_add_one, hx]; simp [entPairs]

theorem key_not_in_take (es : List (net.http.entry GoString Loc)) (i : Nat)
    (x : net.http.entry GoString Loc) (hx : es[i]? = some x)
    (hnd : ((entPairs es).map Prod.fst).Nodup) :
    map.lookupL x.key' (entPairs (es.take i)) = none := by
  rw [map.lookupL_eq_none_iff]
  have hi : i < es.length := (List.getElem?_eq_some_iff.mp hx).1
  have hsplit : es = es.take i ++ x :: es.drop (i + 1) := by
    conv => lhs; rw [← List.take_append_drop i es]
    rw [List.drop_eq_getElem_cons hi]
    rw [List.getElem?_eq_getElem hi] at hx; cases hx; rfl
  rw [hsplit] at hnd
  simp only [entPairs, List.map_append, List.map_cons, List.map_map] at hnd
  have := (List.nodup_append.mp hnd).2.2
  intro hm
  simp only [entPairs, List.map_map] at hm
  exact this _ hm _ (by simp) rfl

theorem lookup_step (es : List (net.http.entry GoString Loc)) (i : Nat)
    (x : net.http.entry GoString Loc) (hx : es[i]? = some x)
    (hnd : ((entPairs es).map Prod.fst).Nodup) (Mi : GMap GoString Loc)
    (hMi : ∀ k', Mi !! k' = map.lookupL k' (entPairs (es.take i))) :
    ∀ k', (GMap.insert x.key' x.value' Mi) !! k' = map.lookupL k' (entPairs (es.take (i + 1))) := by
  intro k'
  rw [entPairs_take_succ es i x hx, lookupL_append_one, GMap.lookup_insert_eq_iff]
  by_cases hk : x.key' = k'
  · subst hk; simp [key_not_in_take es i x hx hnd]
  · simp only [hk, ↓reduceIte, hMi k']
    cases map.lookupL k' (entPairs (es.take i)) <;> simp [Ne.symm hk]

/-- `h.add(k, v)` of a key not among the children (the owner, at `1`). -/
theorem wp_mapping_add (h : Loc) (st : MapSt) (kids : List (GoString × Loc)) (k : GoString)
    (v : Loc) (ms : w64) (hk : map.lookupL k kids = none) :
    {{ globalAddr net.http.maxSlice ↦□ ms ∗ mapRep (GF := GF) (hG := hG) (DFrac.own 1) h st kids }}
      (App (App (Val (h @!! go.GoType.PointerType kidsTy @!! go!"add")) (Val #k)) (Val #v))
    {{ RET #(); ∃ st' : MapSt, mapRep (DFrac.own 1) h st' (kids ++ [(k, v)]) }} := by
  by_cases hm : st.m = map.nil
  · simp only [mapRep, hm, ↓reduceIte]
    wp_start as ⟨#Hms, Hh, %Hnd, #Hes, Hcap, %Hkids⟩
    ihave %hnn := typedPointsto_not_null _ _ _ $$ Hh
    iStructNamedPrefix Hh "H"
    wp_auto
    wp_if_destruct
    · wp_apply (wp_slice_literal (l := [({ key' := k, value' := v } : net.http.entry GoString Loc)]))
      isplitr
      · ipureintro; rfl
      iintro %sl ⟨Hsl, -⟩
      try wp_auto
      wp_apply (wp_slice_append_persistent (V := net.http.entry GoString Loc) st.s st.es _
        [({ key' := k, value' := v } : net.http.entry GoString Loc)] (DFrac.own 1))
        $$ [$Hes $Hcap $Hsl] as %s' ⟨#Hes', Hcap', -⟩
      try wp_auto
      iapply HΦ
      iexists { s := s', m := map.nil, es := st.es ++ [{ key' := k, value' := v }], M := st.M }
      simp only [↓reduceIte]
      ihave Hh := typedPointsto_combine h ({ s' := s', m' := map.nil } : net.http.mapping GoString Loc) (DFrac.own 1) hnn $$ [Hs Hm]
      · simp only [TypedPointsto.typedPointstoDef]; iframe
      iframe; iframe #
      ipureintro
      refine ⟨kids_append_nodup kids k v Hnd hk, ?_⟩
      simp [entPairs, ← Hkids]
    · wp_apply (wp_map_make1 (K := GoString) (V := Loc) go.string _) as %m' HM
      try wp_auto
      ihave %Hlen := ownSlice_len _ _ _ $$ Hes
      ihave HI : (∃ (i : w64) (ev : net.http.entry GoString Loc) (Mi : GMap GoString Loc),
          "i" ∷ i_ptr ↦ i ∗ "e" ∷ e_ptr ↦ ev ∗ "HM" ∷ m' ↦$ Mi ∗
          "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z st.s.len ∧
            ∀ k', Mi !! k' = map.lookupL k' (entPairs (st.es.take (sint.nat i)))⌝ : IProp GF)
          $$ [i e HM]
      · iexists W64 0, _, _
        iframe
        ipureintro
        refine ⟨by word, by word, fun k' => ?_⟩
        rw [show sint.nat (W64 0) = 0 by word]
        simp [entPairs, map.lookupL]
      wp_for HI
      wp_if_destruct
      · try wp_auto
        simp only [Hi.1, Hif, _root_.and_self, ↓reduceIte]
        list_elem st.es (sint.nat i) as x
        wp_apply wp_load_slice_index st.s (sint.Z i) st.es _ x (by word) $$ [Hes] with Hes
        · iframe #; ipureintro; rw [show (sint.Z i).toNat = sint.nat i by word]; exact Hx_lookup
        try wp_auto
        wp_apply (wp_mapInsert (K := GoString) (V := Loc) go.string m' Mi x.key' x.value') $$ HM as HM
        try wp_auto
        wp_for_post
        iframe
        iexists i + W64 1, x, _
        iframe
        ipureintro
        refine ⟨by word, by word, ?_⟩
        rw [show sint.nat (i + W64 1) = sint.nat i + 1 by word]
        exact lookup_step st.es (sint.nat i) x Hx_lookup (by rw [Hkids]; exact Hnd) Mi Hi.2.2
      · have hall : sint.nat i = st.es.length := by word
        wp_apply (wp_mapInsert (K := GoString) (V := Loc) go.string m' Mi k v) $$ HM as HM
        try wp_auto
        ihave %hm'n := ownMap_not_nil _ _ _ $$ HM
        iapply HΦ
        iexists { s := slice.nil, m := m', es := [], M := GMap.insert k v Mi }
        simp only [hm'n, ↓reduceIte]
        ihave Hh := typedPointsto_combine h ({ s' := slice.nil, m' := m' } : net.http.mapping GoString Loc) (DFrac.own 1) hnn $$ [Hs Hm]
        · simp only [TypedPointsto.typedPointstoDef]; iframe
        iframe
        ipureintro
        refine ⟨kids_append_nodup kids k v Hnd hk, fun k' => ?_⟩
        rw [GMap.lookup_insert_eq_iff, lookupL_append_one]
        have hMi := Hi.2.2 k'
        rw [hall, List.take_length, Hkids] at hMi
        by_cases hk' : k = k'
        · subst hk'; simp [hk]
        · simp only [hk', ↓reduceIte, hMi]
          cases map.lookupL k' kids <;> simp [Ne.symm hk']
  · simp only [mapRep, hm, ↓reduceIte]
    wp_start as ⟨#Hms, Hh, %Hnd, HM, %HMk⟩
    ihave %hnn := typedPointsto_not_null _ _ _ $$ Hh
    iStructNamedPrefix Hh "H"
    wp_auto
    rw [decide_eq_false hm]
    wp_auto
    rw [decide_eq_false hm]
    wp_auto
    wp_apply (wp_mapInsert (K := GoString) (V := Loc) go.string st.m st.M k v) $$ HM as HM
    try wp_auto
    iapply HΦ
    iexists { s := st.s, m := st.m, es := st.es, M := GMap.insert k v st.M }
    simp only [hm, ↓reduceIte]
    ihave Hh := typedPointsto_combine h ({ s' := st.s, m' := st.m } : net.http.mapping GoString Loc) (DFrac.own 1) hnn $$ [Hs Hm]
    · simp only [TypedPointsto.typedPointstoDef]; iframe
    iframe
    ipureintro
    refine ⟨kids_append_nodup kids k v Hnd hk, fun k' => ?_⟩
    rw [GMap.lookup_insert_eq_iff, lookupL_append_one, HMk k']
    by_cases hk' : k = k'
    · subst hk'; simp [hk]
    · simp only [hk', ↓reduceIte]
      cases map.lookupL k' kids <;> simp [Ne.symm hk']


theorem TreeSt.okP_locOf (root : Loc) (S : TreeSt) (kc k : List Seg) (hok : S.okP root kc) :
    (locOf (S.nodes !! k) = null → S.nodes !! k = none) ∧
    (locOf (S.nodes !! k) ≠ null → ∃ d, S.nodes !! k = some d ∧ d.l = locOf (S.nodes !! k)) := by
  cases h : S.nodes !! k with
  | none => exact ⟨fun _ => rfl, fun h' => absurd rfl h'⟩
  | some d =>
    have := (hok.2.2.2.2.2.2.2 k d h).1
    exact ⟨fun h' => absurd h' (by simpa [locOf] using this), fun _ => ⟨d, rfl, by simp [locOf]⟩⟩

theorem gmap_insert_same {K V : Type} [DecidableEq K] (m : GMap K V) (k : K) (v : V)
    (h : m !! k = some v) : <[k := v]> m = m :=
  GMap.ext (fun k' => by rw [GMap.lookup_insert_eq_iff]; by_cases hk : k = k' <;> simp [hk, ← h])

/-- A fresh node's fields (`&routingNode{}`). -/
theorem freshNode_rep (c : Loc) :
    c ↦ (zero_val net.http.routingNode) ⊢
      nodeRep (GF := GF) (hG := hG) (DFrac.own 1) (freshNode c) ∗ ⌜c ≠ null⌝ := by
  iintro Hc
  ihave %hcn := typedPointsto_not_null _ _ _ $$ Hc
  iStructNamed Hc
  iunfold nodeRep
  simp only [freshNode, mapRep, ↓reduceIte]
  iframe
  isplitl []
  · isplitr
    · ipureintro; exact List.nodup_nil
    isplitr
    · iapply ownSlice_nil
    isplitl []
    · iapply ownSliceCap_nil
    ipureintro; rfl
  ipureintro; exact hcn

/-- `n.addChild(key)` at the node `kc` (the owner, every node at `1`). -/
theorem wp_addChild (root : Loc) (S : TreeSt) (kc : List Seg) (d : NodeSt) (key : List w8)
    (ms : w64) (hok : S.okP root kc) (hd : S.nodes !! kc = some d) :
    {{ globalAddr net.http.maxSlice ↦□ ms ∗
        [∗map] _k ↦ d ∈ S.nodes, nodeRep (GF := GF) (hG := hG) (DFrac.own 1) d }}
      (App (Val (d.l @!! go.GoType.PointerType net.http.routingNode.ty @!! go!"addChild")) (Val #key))
    {{ (c : Loc), RET #c; ∃ (N : GMap (List Seg) NodeSt) (d' : NodeSt),
        ([∗map] _k ↦ d ∈ N, nodeRep (DFrac.own 1) d) ∗
        ⌜TreeSt.okP root (TreeSt.mk N S.pats) (kc ++ [.lit key]) ∧ N !! (kc ++ [.lit key]) = some d' ∧
          d'.l = c⌝ }} := by
  wp_start as ⟨#Hms, HN⟩
  icases BigSepM.bigSepM_insert_acc (Φ := fun _ d => nodeRep (GF := GF) (hG := hG) (DFrac.own 1) d) hd $$ HN
    with ⟨Hd, HN⟩
  obtain ⟨n1, n2, n3, n4, n5, n6⟩ := hok.2.2.2.2.2.2.2 kc d hd
  by_cases hk : key = []
  · subst hk
    iunfold nodeRep at Hd
    icases Hd with ⟨Hp, Hh, Hc, Hm, He⟩
    wp_auto
    obtain ⟨hl1, hl2⟩ := TreeSt.okP_locOf root S kc (kc ++ [.lit []]) hok
    wp_if_destruct
    · -- no empty child: a fresh one
      have hnone : S.nodes !! (kc ++ [.lit []]) = none := hl1 (by rw [← n3]; exact Hif)
      icases freshNode_rep «$r0_ptr» $$ «$r0» with ⟨Hfr, %hcn⟩
      ihave Hd' : nodeRep (DFrac.own 1) (linkUpd d (.lit []) «$r0_ptr» d.ms) $$ [Hp Hh Hc Hm He]
      · iunfold nodeRep; simp only [linkUpd]; iframe
      ispecialize HN $$ Hd'
      have hfr : Iris.Std.PartialMap.get? (Std.insert S.nodes kc (linkUpd d (.lit []) «$r0_ptr» d.ms))
          (kc ++ [.lit []]) = none := by
        show (<[kc := linkUpd d (.lit []) «$r0_ptr» d.ms]> S.nodes) !! (kc ++ [.lit []]) = none
        rw [GMap.lookup_insert_ne _ _ (append_single_ne kc _)]; exact hnone
      ihave HN := (BigSepM.bigSepM_insert (Φ := fun _ d => nodeRep (GF := GF) (hG := hG) (DFrac.own 1) d)
        (x := freshNode «$r0_ptr») hfr).2 $$ [Hfr HN]
      · iframe
      iapply HΦ
      iexists _, freshNode «$r0_ptr»
      iframe
      ipureintro
      refine ⟨TreeSt.okP_addNode root S kc (.lit []) hok d hd hnone «$r0_ptr» hcn d.ms, ?_, rfl⟩
      exact GMap.lookup_insert _ _ _
    · -- the empty child
      obtain ⟨d2, hd2, hl2⟩ := hl2 (by rw [← n3]; exact Hif)
      ihave Hd' : nodeRep (DFrac.own 1) d $$ [Hp Hh Hc Hm He]
      · iunfold nodeRep; iframe
      ispecialize HN $$ Hd'
      rw [show Std.insert S.nodes kc d = S.nodes from gmap_insert_same S.nodes kc d hd]
      iapply HΦ
      iexists S.nodes, d2
      iframe
      ipureintro
      refine ⟨TreeSt.okP_mono root S kc _ hok (by rw [hd2]; rfl), hd2, by rw [hl2, n3]⟩
  · obtain ⟨b, bs, rfl⟩ := List.exists_cons_of_ne_nil hk
    wp_auto
    wp_apply wp_findChild (DFrac.own 1) d (b :: bs) $$ Hd as Hd
    have hlk := n2 (b :: bs) hk
    cases hc : map.lookupL (b :: bs) d.kids with
    | some c =>
      obtain ⟨d2, hd2, hl2⟩ : ∃ d2, S.nodes !! (kc ++ [.lit (b :: bs)]) = some d2 ∧ d2.l = c := by
        rw [hc] at hlk
        cases h2 : S.nodes !! (kc ++ [.lit (b :: bs)]) with
        | none => rw [h2] at hlk; simp at hlk
        | some d2 => rw [h2] at hlk; simp at hlk; exact ⟨d2, rfl, hlk.symm⟩
      have hcn : c ≠ null := by rw [← hl2]; exact (hok.2.2.2.2.2.2.2 _ d2 hd2).1
      simp only [Option.getD_some, decide_eq_false hcn]
      try wp_auto
      ispecialize HN $$ Hd
      rw [show Std.insert S.nodes kc d = S.nodes from gmap_insert_same S.nodes kc d hd]
      iapply HΦ
      iexists S.nodes, d2
      iframe
      ipureintro
      exact ⟨TreeSt.okP_mono root S kc _ hok (by rw [hd2]; rfl), hd2, hl2⟩
    | none =>
      have hnone : S.nodes !! (kc ++ [.lit (b :: bs)]) = none := by
        rw [hc] at hlk
        cases h2 : S.nodes !! (kc ++ [.lit (b :: bs)]) with
        | none => rfl
        | some d2 => rw [h2] at hlk; simp at hlk
      simp only [Option.getD_none]
      wp_auto
      iunfold nodeRep at Hd
      icases Hd with ⟨Hp, Hh, Hc, Hm, He⟩
      wp_apply wp_mapping_add _ d.ms d.kids (b :: bs) «$r0_ptr» ms hc $$ [$Hms $Hc] as ⟨%st', Hc⟩
      try wp_auto
      icases freshNode_rep «$r0_ptr» $$ «$r0» with ⟨Hfr, %hcn⟩
      ihave Hd' : nodeRep (DFrac.own 1) (linkUpd d (.lit (b :: bs)) «$r0_ptr» st') $$ [Hp Hh Hc Hm He]
      · iunfold nodeRep; simp only [linkUpd]; iframe
      ispecialize HN $$ Hd'
      have hfr : Iris.Std.PartialMap.get? (Std.insert S.nodes kc (linkUpd d (.lit (b :: bs)) «$r0_ptr» st'))
          (kc ++ [.lit (b :: bs)]) = none := by
        show (<[kc := linkUpd d (.lit (b :: bs)) «$r0_ptr» st']> S.nodes) !! (kc ++ [.lit (b :: bs)]) = none
        rw [GMap.lookup_insert_ne _ _ (append_single_ne kc _)]; exact hnone
      ihave HN := (BigSepM.bigSepM_insert (Φ := fun _ d => nodeRep (GF := GF) (hG := hG) (DFrac.own 1) d)
        (x := freshNode «$r0_ptr») hfr).2 $$ [Hfr HN]
      · iframe
      iapply HΦ
      iexists _, freshNode «$r0_ptr»
      iframe
      ipureintro
      refine ⟨TreeSt.okP_addNode root S kc (.lit (b :: bs)) hok d hd hnone «$r0_ptr» hcn st', ?_, rfl⟩
      exact GMap.lookup_insert _ _ _

/-- `n.set(pp, h)` on a node without a pattern. -/
theorem wp_set (d : NodeSt) (pp : Loc) (h : GoInterface) (hnil : d.pat = null ∧ d.h = interface.nil) :
    {{ nodeRep (GF := GF) (hG := hG) (DFrac.own 1) d }}
      (App (App (Val (d.l @!! go.GoType.PointerType net.http.routingNode.ty @!! go!"set")) (Val #pp)) (Val #h))
    {{ RET #(); nodeRep (DFrac.own 1) (setPat d pp h) }} := by
  unfold nodeRep
  obtain ⟨hp0, hh0⟩ := hnil
  wp_start as ⟨Hp, Hh, Hc, Hm, He⟩
  wp_auto
  rw [hp0, hh0]
  wp_auto
  iapply HΦ
  simp only [setPat]
  iframe

end wp

end net.http
end Perennial

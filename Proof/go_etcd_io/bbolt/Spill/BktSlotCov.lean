/-
`Bucket.spill` (U9p, `notes/bbolt-proof-plan.md`): **a nested bucket's unspilled tree at the start
of the spill, by its pages** (`uTree_start_pieces`, used by `Spill/BktSlot`). Each slot of the
tree is in the extent of one view page, a *piece* (`Pc`), owned by a node of the tree (its page) or
by a page position of one of its nodes (a page of the position's subtree). Two pieces of disjoint
owners are distinct pages (`Pc_disj`: a page is one node's by the page cache, no node's page is
under a page position, `posNodeFree`, and distinct positions' subtrees are disjoint,
`posDisjoint`), and distinct pages have disjoint extents (`pagesDisjoint`), so the tree's slots are
distinct. A piece's page is a position of the bucket with its page's extent
(`Pc_cov`: a node's page by `node_pos`; a page under a page position through its branches, the
leaves there plain, `posShape`), so the slot is covered.
-/
module

public import Proof.go_etcd_io.bbolt.Spill.UTree
public import Proof.go_etcd_io.bbolt.Rebalance.RblXSPos

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove
namespace bbolt

open go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

namespace Spill

section cov
variable [GooseExts]

/-! ## Lists -/

theorem nodup_idx' {α : Type} : ∀ {l : List α} {i j : Nat} {a : α}, l.Nodup → l[i]? = some a →
    l[j]? = some a → i = j
  | [], _, _, _, _, h, _ => by simp at h
  | b :: l, 0, 0, _, _, _, _ => rfl
  | b :: l, 0, j + 1, a, hn, hi, hj => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
    subst hi
    simp only [List.getElem?_cons_succ] at hj
    exact absurd (List.mem_of_getElem? hj) (List.nodup_cons.1 hn).1
  | b :: l, i + 1, 0, a, hn, hi, hj => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
    subst hj
    simp only [List.getElem?_cons_succ] at hi
    exact absurd (List.mem_of_getElem? hi) (List.nodup_cons.1 hn).1
  | b :: l, i + 1, j + 1, a, hn, hi, hj => by
    simp only [List.getElem?_cons_succ] at hi hj
    rw [nodup_idx' (List.nodup_cons.1 hn).2 hi hj]

theorem nodup_flatMap_of' {α β : Type} (f : α → List β) :
    ∀ (l : List α), (∀ a ∈ l, (f a).Nodup) →
      (∀ (i j : Nat) a b x, i < j → l[i]? = some a → l[j]? = some b → x ∈ f a → x ∉ f b) →
      (l.flatMap f).Nodup
  | [], _, _ => List.nodup_nil
  | a :: l, h1, h2 => by
    rw [List.flatMap_cons, List.nodup_append]
    refine ⟨h1 a List.mem_cons_self, nodup_flatMap_of' f l (fun b hb => h1 b
      (List.mem_cons_of_mem _ hb)) (fun i j x y z hij hx hy => h2 (i + 1) (j + 1) x y z (by omega)
      (by simpa using hx) (by simpa using hy)), ?_⟩
    intro x hx y hy hxy
    subst hxy
    obtain ⟨b, hb, hxb⟩ := List.mem_flatMap.1 hy
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hb
    exact h2 0 (j + 1) a _ x (by omega) rfl (by simp [hj]) hx hxb

/-- Distinct positions of a distinct `flatMap` have disjoint images. -/
theorem flatMap_nodup_disj {α β : Type} (f : α → List β) :
    ∀ (l : List α) (i j : Nat) (a b : α) (x : β), (l.flatMap f).Nodup → i < j → l[i]? = some a →
      l[j]? = some b → x ∈ f a → x ∉ f b
  | [], _, _, _, _, _, _, _, h, _, _ => by simp at h
  | _ :: _, _, 0, _, _, _, _, hij, _, _, _ => absurd hij (Nat.not_lt_zero _)
  | c :: l, 0, j + 1, a, b, x, hn, _, ha, hb, hxa => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at ha
    subst ha
    simp only [List.getElem?_cons_succ] at hb
    rw [List.flatMap_cons, List.nodup_append] at hn
    intro hxb
    exact hn.2.2 x hxa x (List.mem_flatMap.2 ⟨b, List.mem_of_getElem? hb, hxb⟩) rfl
  | c :: l, i + 1, j + 1, a, b, x, hn, hij, ha, hb, hxa => by
    simp only [List.getElem?_cons_succ] at ha hb
    rw [List.flatMap_cons, List.nodup_append] at hn
    exact flatMap_nodup_disj f l i j a b x hn.2.1 (by omega) ha hb hxa

theorem w64_cast_toNat {p : Nat} (h : p < 2 ^ 64) : (W64 (p : Int)).toNat = p := by
  simp only [BitVec.toNat_ofInt]; omega

/-! ## Pieces -/

/-- **Page `p` is owned** by a node `l` with `NS l` (its page) or by a page position `(l, k)` with
`PS l k` (a page of its subtree), in bucket `B`. -/
def OwnP (v : View) (B : BRec) (NS : Loc → Prop) (PS : Loc → Nat → Prop) (p : Nat) : Prop :=
  (∃ l r, NS l ∧ B.ns !! l = some r ∧ r.nv.pgid' ≠ W64 0 ∧ r.nv.pgid'.toNat = p) ∨
  (∃ l k q, PS l k ∧ pagePosAt B l k q ∧ treeHas v.pages q.toNat p)

/-- **Slot `s` is in an owned view page's extent.** -/
def Pc (v : View) (B : BRec) (NS : Loc → Prop) (PS : Loc → Nat → Prop) (s : Nat) : Prop :=
  ∃ p pg, v.pages !! p = some pg ∧ p ≤ s ∧ s < p + (1 + pageOverflow pg) ∧ OwnP v B NS PS p

theorem Pc_mono {v : View} {B : BRec} {NS NS' : Loc → Prop} {PS PS' : Loc → Nat → Prop}
    (hN : ∀ l, NS l → NS' l) (hP : ∀ l k, PS l k → PS' l k) {s : Nat} (h : Pc v B NS PS s) :
    Pc v B NS' PS' s := by
  obtain ⟨p, pg, hpg, h1, h2, ho⟩ := h
  refine ⟨p, pg, hpg, h1, h2, ?_⟩
  rcases ho with ⟨l, r, hl, hr, h0, he⟩ | ⟨l, k, q, hl, hq, ht⟩
  · exact Or.inl ⟨l, r, hN l hl, hr, h0, he⟩
  · exact Or.inr ⟨l, k, q, hP l k hl, hq, ht⟩

/-- **Pieces of disjoint owners are distinct slots.** -/
theorem Pc_disj {v : View} {hwm : Nat} {bl : Loc} {B : BRec} (hcl : bktClean v hwm bl B)
    (hpd : pagesDisjoint v.pages) {NS1 NS2 : Loc → Prop} {PS1 PS2 : Loc → Nat → Prop}
    (hN : ∀ l, NS1 l → NS2 l → False) (hP : ∀ l k, PS1 l k → PS2 l k → False) {s : Nat}
    (h1 : Pc v B NS1 PS1 s) (h2 : Pc v B NS2 PS2 s) : False := by
  obtain ⟨p1, pg1, hpg1, a1, b1, ho1⟩ := h1
  obtain ⟨p2, pg2, hpg2, a2, b2, ho2⟩ := h2
  have hp : p1 = p2 := by
    apply Classical.byContradiction; intro hne
    rcases hpd p1 pg1 p2 pg2 hpg1 hpg2 hne with h | h <;> omega
  subst hp
  have hnm : ∀ l r, B.ns !! l = some r → B.nm !! r.nv.pgid' = some l :=
    fun l r hr => (hcl.2.2.2.2.2.2.2.1 l r hr).2.2.2.2.2.2.2.1
  have hfree := hcl.2.2.2.2.2.2.2.2.2.1
  rcases ho1 with ⟨l1, r1, hl1, hr1, -, he1⟩ | ⟨l1, k1, q1, hl1, hq1, ht1⟩ <;>
    rcases ho2 with ⟨l2, r2, hl2, hr2, -, he2⟩ | ⟨l2, k2, q2, hl2, hq2, ht2⟩
  · have e : r1.nv.pgid' = r2.nv.pgid' := BitVec.eq_of_toNat_eq (by rw [he1, he2])
    have h1 := hnm l1 r1 hr1
    rw [e, hnm l2 r2 hr2] at h1
    obtain rfl := Option.some.inj h1
    exact hN _ hl1 hl2
  · have := hfree l2 k2 q2 hq2 _ ht2
    rw [← he1, w64_toNat_cast, hnm l1 r1 hr1] at this; cases this
  · have := hfree l1 k1 q1 hq1 _ ht1
    rw [← he2, w64_toNat_cast, hnm l2 r2 hr2] at this; cases this
  · by_cases he : (l1, k1) = (l2, k2)
    · simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact hP l1 k1 hl1 hl2
    · exact hcl.2.2.2.2.2.2.2.2.1 l1 k1 q1 l2 k2 q2 hq1 hq2 he _ ht1 ht2

/-- A list of pieces of distinct entries is distinct. -/
theorem Pc_nodup_flatMap {v : View} {hwm : Nat} {bl : Loc} {B : BRec} (hcl : bktClean v hwm bl B)
    (hpd : pagesDisjoint v.pages) {α : Type} (f : α → List Nat) (NS : Nat → α → Loc → Prop)
    (PS : Nat → α → Loc → Nat → Prop) (l : List α) (hnd : ∀ a ∈ l, (f a).Nodup)
    (hpc : ∀ i a, l[i]? = some a → ∀ s ∈ f a, Pc v B (NS i a) (PS i a) s)
    (hdN : ∀ i j a b, i < j → l[i]? = some a → l[j]? = some b → ∀ x, NS i a x → NS j b x → False)
    (hdP : ∀ i j a b, i < j → l[i]? = some a → l[j]? = some b → ∀ x k, PS i a x k → PS j b x k →
      False) :
    (l.flatMap f).Nodup :=
  nodup_flatMap_of' f l hnd fun i j a b x hij ha hb hxa hxb =>
    Pc_disj hcl hpd (hdN i j a b hij ha hb) (hdP i j a b hij ha hb) (hpc i a ha x hxa)
      (hpc j b hb x hxb)

/-- The slots of distinct pages of `P` are distinct (`pgSlots`). -/
theorem pgSlots_nodup {P : Pages} (hpd : pagesDisjoint P) {S : List Nat} (hS : S.Nodup)
    (hP : ∀ x ∈ S, (P !! x).isSome) : (pgSlots P S).Nodup := by
  unfold pgSlots
  refine nodup_flatMap_of' _ S (fun x _ => ?_) ?_
  · cases P !! x with
    | some pg => exact List.nodup_range'
    | none => simp
  · intro i j a b x hij ha hb hxa hxb
    have hne : a ≠ b := by
      intro e; subst e
      have := nodup_idx' hS ha hb; omega
    obtain ⟨pga, hpa⟩ := Option.isSome_iff_exists.1 (hP a (List.mem_of_getElem? ha))
    obtain ⟨pgb, hpb⟩ := Option.isSome_iff_exists.1 (hP b (List.mem_of_getElem? hb))
    rw [hpa] at hxa; rw [hpb] at hxb
    simp only [List.mem_range'] at hxa hxb
    rcases hpd a pga b pgb hpa hpb hne with h | h <;> omega

/-- A slot of `pgSlots` of pages of `P` is in one of their extents. -/
theorem mem_pgSlots {P : Pages} {S : List Nat} (hP : ∀ x ∈ S, (P !! x).isSome) {s : Nat}
    (hs : s ∈ pgSlots P S) : ∃ x ∈ S, ∃ pg, P !! x = some pg ∧ x ≤ s ∧ s < x + (1 + pageOverflow pg) := by
  unfold pgSlots at hs
  obtain ⟨x, hx, hsx⟩ := List.mem_flatMap.1 hs
  obtain ⟨pg, hpg⟩ := Option.isSome_iff_exists.1 (hP x hx)
  rw [hpg] at hsx
  simp only [List.mem_range'] at hsx
  obtain ⟨k, hk, rfl⟩ := hsx
  exact ⟨x, hx, pg, hpg, by omega, by omega⟩

/-! ## Coverage by positions -/

/-- Below a root whose leaves hold no nested bucket, a page of the tree is a page of the root's own
tree (`ownHas`). -/
theorem ownHas_of_treeHas {P : Pages} {q : Nat}
    (hpl : ∀ p pg, ownHas P q p → P !! p = some pg → pageFlags pg = leafPageFlag →
      ∀ i < pageCount pg, leafFlags pg i % 2 ≠ bucketLeafFlag) {x : Nat} (h : treeHas P q x) :
    ownHas P q x :=
  treeHas.rec (pages := P)
    (motive_1 := fun a b _ => (∀ p, ownHas P a p → ownHas P q p) → ownHas P q b)
    (motive_2 := fun pg b _ => ∀ a, P !! a = some pg → (∀ p, ownHas P a p → ownHas P q p) →
      ownHas P q b)
    (motive_3 := fun _ _ _ => True)
    (fun a pg hpg hA => hA a (ownHas.root a pg hpg))
    (fun a _ _ hpg _ ih hA => ih a hpg hA)
    (fun pg i _ hfl hi _ ih a hpa hA =>
      ih (fun p hp => hA p (ownHas.child a pg i p hpa hfl hi hp)))
    (fun pg i _ hfl hi hbf _ _ a hpa hA =>
      absurd hbf (hpl a pg (hA a (ownHas.root a pg hpa)) hpa hfl i hi))
    (fun _ _ _ _ _ => trivial)
    (fun _ _ _ _ _ => trivial)
    h (fun _ hp => hp)

theorem ownHas_page {P : Pages} {r x : Nat} (h : ownHas P r x) : ∃ pg, P !! r = some pg := by
  cases h with
  | root _ pg hpg => exact ⟨pg, hpg⟩
  | child _ pg _ _ hpg _ _ _ => exact ⟨pg, hpg⟩

/-- **The pages under an unmaterialized position are positions.** -/
theorem pos_ownHas {X : WX} {c : Loc} {B : BRec} (hb : X.t.bs !! c = some B)
    (h0 : B.ib.root' ≠ W64 0) (h64 : ∀ p pg, X.v.pages !! p = some pg → p < 2 ^ 64)
    {t : RTree} (ht : ltIs (ltree X) c t) {q0 : w64}
    (hfree : ∀ d, treeHas X.v.pages q0.toNat d → B.nm !! W64 (d : Int) = none) :
    ∀ a x, ownHas X.v.pages a x → treeHas X.v.pages q0.toNat a → W64 (a : Int) ∈ t.pos →
      W64 (x : Int) ∈ t.pos := by
  intro a x h
  induction h with
  | root _ _ _ => exact fun _ h => h
  | child a pg i x hpa hfl hi hown ih =>
    intro hta hpos
    have ha64 := h64 a pg hpa
    have hL := ltree_unmat X c B hb h0 (W64 (a : Int)) (hfree a hta) pg
      (by rw [w64_cast_toNat ha64]; exact hpa)
    have hfl' : decide (pageFlags pg = leafPageFlag) = false := by
      rw [hfl]; decide
    rw [hfl'] at hL
    have hm : pageW pg i ∈ pageWs pg := List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩
    have hc := pos_child (ltree X) c t ht _ hpos _ hL _ hm
    rw [pageW_pgid_branch pg i hfl] at hc
    obtain ⟨cpg, hcpg⟩ := ownHas_page hown
    exact ih (treeHas_trans hta (treeHas_child hpa hfl hi (treeHas.root _ cpg hcpg))) hc

/-- **A piece of a nested bucket at the start of the spill is covered by a position.** -/
theorem Pc_cov {X : WX} {fl : FLPg} (hpre : spillPre X fl) (hreach : liveReach X)
    (hv : flViewU X fl) {c : Loc} {B : BRec} (hc : X.t.bs !! c = some B) (hne : c ≠ X.rl)
    {NS : Loc → Prop} {PS : Loc → Nat → Prop} {s : Nat} (h : Pc X.v B NS PS s) :
    ∃ pid, coverW X s (.pos c pid) := by
  have hok := hpre.1
  have hcl : bktClean X.v X.t.mv.pgid'.toNat c B := (hok.1.2.2.2.2.2 c B hc).1
  have hrt := hpre.2.2.2.1 c (by rw [hc]; simp)
  obtain ⟨t, ht, htp, hth, -⟩ := hrt
  have hposeq := positions_rt X c t ht htp hth
  obtain ⟨bnd, hbk⟩ := (hok.2.1 c B hc).1
  have h64 : ∀ p pg, X.v.pages !! p = some pg → p < 2 ^ 64 := by
    intro p pg hp; have := hv.2.2.1 p pg hp; omega
  have hbn : X.t.bs !! c ≠ none := by rw [hc]; simp
  obtain ⟨p, pg, hpg, h1, h2, ho⟩ := h
  rcases ho with ⟨l, r, -, hr, hp0, he⟩ | ⟨l, k, q, -, hpp, htq⟩
  · have h0 : B.ib.root' ≠ W64 0 := fun e =>
      hp0 ((hcl.2.2.2.2.2.2.2.1 l r hr).2.2.2.2.2.2.2.2.1 e)
    have hlive := wOKR_nsLive X hok c B l r hc hr
    obtain ⟨rt, hrtI, hd⟩ := hreach.2 c B l r hc hr hlive
    have hpos := node_pos X c B hc hcl hbk.2.1 (hpre.2.2.2.1 c hbn) h0 rt l hrtI hd r hr
    have hpg' : X.v.pages !! r.nv.pgid'.toNat = some pg := by rw [he]; exact hpg
    have hext := posExtent_node X c B hc hcl h0 l r hr hp0 pg hpg'
    exact ⟨r.nv.pgid', hbn, hpos, _, hext, by simp only; omega, by simp only; omega⟩
  · obtain ⟨rl', w, hrl, hlf, hw, hwq, hnm⟩ := hpp
    have h0 : B.ib.root' ≠ W64 0 := by
      intro e; have := hcl.2.2.2.2.2.2.1 e l rl' hrl; rw [hlf] at this; cases this
    have hlive := wOKR_nsLive X hok c B l rl' hc hrl
    obtain ⟨rt, hrtI, hd⟩ := hreach.2 c B l rl' hc hrl hlive
    have hpos := node_pos X c B hc hcl hbk.2.1 (hpre.2.2.2.1 c hbn) h0 rt l hrtI hd rl' hrl
    rw [hposeq] at hpos
    have hL := ltree_node X c B hc hcl h0 l rl' hrl
    rw [hlf] at hL
    have hq := pos_child (ltree X) c t ht _ hpos rl'.ws hL w (List.mem_of_getElem? hw)
    rw [hwq] at hq
    have hpp : pagePosAt B l k q := ⟨rl', w, hrl, hlf, hw, hwq, hnm⟩
    have hpr : posRoot B q.toNat :=
      Or.inr ⟨l, k, by rw [w64_toNat_cast]; exact hpp, q.isLt⟩
    have hpl : ∀ p' pg', ownHas X.v.pages q.toNat p' → X.v.pages !! p' = some pg' →
        pageFlags pg' = leafPageFlag → ∀ i < pageCount pg', leafFlags pg' i % 2 ≠ bucketLeafFlag :=
      fun p' pg' ho hp hl i hi he => hne ((hok.1.2.1.2.2.2.1 c B hc q.toNat p' pg' hpr ho hp hl i hi).1.1 he)
    have hown := ownHas_of_treeHas hpl htq
    have hfree : ∀ d, treeHas X.v.pages q.toNat d → B.nm !! W64 (d : Int) = none :=
      fun d hd => hcl.2.2.2.2.2.2.2.2.2.1 l k q hpp d hd
    obtain ⟨qpg, hqpg⟩ := ownHas_page hown
    have hpp_pos := pos_ownHas hc h0 h64 ht hfree q.toNat p hown (treeHas.root _ qpg hqpg)
      (by rw [w64_toNat_cast]; exact hq)
    have hp64 := h64 p pg hpg
    have hp2 : 2 ≤ p := (hv.1.2.1.2 p ⟨p, pg, hpg, Nat.le_refl p, by omega⟩).1
    have hpne : W64 (p : Int) ≠ W64 0 := by
      intro e; have := congrArg BitVec.toNat e
      rw [w64_cast_toNat hp64] at this; simp at this; omega
    have hext : X.posExtent c (W64 (p : Int)) = some (W64 (p : Int), 1 + pageOverflow pg) := by
      unfold WX.posExtent
      rw [hc]
      simp only [resolve, h0, ↓reduceIte, hfree p htq, hpne, w64_cast_toNat hp64, hpg,
        Option.map_some]
    refine ⟨W64 (p : Int), hbn, by rw [hposeq]; exact hpp_pos, _, hext, ?_, ?_⟩ <;>
      simp only [w64_cast_toNat hp64] <;> omega

/-! ## The pieces of an unspilled tree -/

theorem node_ns {X : WX} {c n : Loc} {B : BRec} {r : NRec} (hc : X.t.bs !! c = some B)
    (h : X.node c n = some r) : B.ns !! n = some r := by
  unfold WX.node at h; rw [hc] at h; exact h

/-- A node's own page slots are a piece of the node. -/
theorem ownSl_pc {v : View} {B : BRec} {n : Loc} {r : NRec} (hr : B.ns !! n = some r)
    (hown : ownPg v r.nv.pgid') :
    (ownSl v r.nv.pgid').Nodup ∧ ∀ s ∈ ownSl v r.nv.pgid', Pc v B (· = n) (fun _ _ => False) s := by
  unfold ownSl
  by_cases h0 : r.nv.pgid' = W64 0
  · simp [h0]
  · simp only [h0, ↓reduceIte]
    obtain ⟨pg, hpg, -⟩ := hown h0
    simp only [pgSlots, List.flatMap_cons, List.flatMap_nil, List.append_nil, hpg]
    refine ⟨List.nodup_range', fun s hs => ?_⟩
    simp only [List.mem_range'] at hs
    obtain ⟨k, hk, rfl⟩ := hs
    exact ⟨_, pg, hpg, by omega, by omega, Or.inl ⟨n, r, rfl, hr, h0, rfl⟩⟩

theorem uEnt_child_of {X : WX} {bl : Loc} {P : Pages} {hwm : Nat} {n : Loc}
    {lo hi : Option (List w8)} {ws : List WEntry} {cs : List Loc} {h i : Nat} {w : WEntry}
    {e : UE} (he : uEnt X bl P hwm n lo hi ws cs h i w e) {c : Loc} (hc : e.ch = some c) :
    ∃ rc, X.node bl c = some rc ∧ rc.nv.pgid' = w.pgid := by
  cases he with
  | child _ _ _ _ _ _ _ _ c2 rc _ _ _ _ _ hnode _ hpgid _ _ _ _ =>
    simp only [Option.some.injEq] at hc
    subst hc
    exact ⟨rc, hnode, hpgid⟩
  | fin => simp at hc

/-- **A finished entry's page is not materialized** (at the start: no spilled node). -/
theorem fin_unmat {X : WX} {c : Loc} {B : BRec} {hwm' : Nat} (hcl : bktClean X.v hwm' c B)
    (hc : X.t.bs !! c = some B) {P : Pages} {hwm : Nat} {n : Loc} {r : NRec}
    {lo hi : Option (List w8)} {h : Nat} {es : List UE}
    (hr : B.ns !! n = some r) (hlf : r.nv.isLeaf' = false) (hlen : es.length = r.ws.length)
    (hent : ∀ i w e, r.ws[i]? = some w → es[i]? = some e → uEnt X c P hwm n lo hi r.ws r.cs h i w e)
    (hcsE : ∀ c' ∈ r.cs, (∃ e ∈ es, e.ch = some c') ∨ spilledN X c c')
    {i : Nat} {w : WEntry} {e : UE} (hw : r.ws[i]? = some w) (he : es[i]? = some e)
    (hch : e.ch = none) : B.nm !! w.pgid = none := by
  have hnc := hcl.2.2.2.2.2.2.2.1 n r hr
  obtain ⟨-, hpnd, hall⟩ := hnc.2.2.2.2.2.2.2.2.2.2.2.2.1 hlf
  cases hm : B.nm !! w.pgid with
  | none => rfl
  | some l' =>
    exfalso
    obtain ⟨r', hr', hpar⟩ := (hall w (List.mem_of_getElem? hw)).2.1 l' hm
    have hnn : n ≠ null := (hcl.2.2.2.2.1 _ n hnc.2.2.2.2.2.2.2.1).1
    have hnc' := hcl.2.2.2.2.2.2.2.1 l' r' hr'
    obtain ⟨rp, hrp, -, hin, -⟩ := hnc'.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (by rw [hpar]; exact hnn)
    rw [hpar, hr] at hrp; cases hrp
    obtain ⟨-, r'', hr'', hpg''⟩ := hcl.2.2.2.2.1 _ _ hm
    rw [hr'] at hr''; cases hr''
    rcases hcsE l' hin with ⟨e', he'm, he'c⟩ | ⟨-, rc, hrc, -, hsp, -⟩
    · obtain ⟨j, hj, hjeq⟩ := List.getElem_of_mem he'm
      have hj' : r.ws.length > j := by omega
      have hwj : r.ws[j]? = some r.ws[j] := List.getElem?_eq_getElem hj'
      have hej : es[j]? = some e' := by rw [List.getElem?_eq_getElem hj, hjeq]
      obtain ⟨rc, hnode, hpgid⟩ := uEnt_child_of (hent j _ _ hwj hej) he'c
      rw [node_ns hc hnode] at hr'; cases hr'
      have e1 : (r.ws.map WEntry.pgid)[i]? = some w.pgid := by simp [hw]
      have e2 : (r.ws.map WEntry.pgid)[j]? = some w.pgid := by
        simp only [List.getElem?_map, hwj, Option.map_some]; rw [← hpgid, hpg'']
      have hij := nodup_idx' hpnd e1 e2
      subst hij
      rw [hej] at he; cases he
      rw [hch] at he'c; cases he'c
    · rw [node_ns hc hrc] at hr'; cases hr'
      rw [hnc'.2.2.2.2.2.2.1] at hsp; cases hsp

/-- **An unspilled tree's slots are distinct pieces of its own** (a bucket whose leaves hold no
nested bucket, at the start: no spilled node, every page of the tree a view page). -/
theorem uTree_pieces {X : WX} {c : Loc} {B : BRec} {hwm' : Nat} (hcl : bktClean X.v hwm' c B)
    (hc : X.t.bs !! c = some B) (hpd : pagesDisjoint X.v.pages)
    (hnb : ∀ l r, B.ns !! l = some r → r.nv.isLeaf' = true → ∀ w ∈ r.ws, ¬ isBktFlag w.flags)
    {hwm : Nat} {n : Loc} {lo hi : Option (List w8)} {h : Nat} {F D : List Nat} {N : List Loc}
    {E : List El} (hu : uTree X c X.v.pages hwm n lo hi h F D N E) :
    D.Nodup ∧ ∀ s ∈ D, Pc X.v B (· ∈ N) (fun l _ => l ∈ N) s :=
  uTree.rec (X := X) (bl := c) (P := X.v.pages) (hwm := hwm)
    (motive_1 := fun _ _ _ _ _ D N _ _ =>
      D.Nodup ∧ ∀ s ∈ D, Pc X.v B (· ∈ N) (fun l _ => l ∈ N) s)
    (motive_2 := fun n _ _ _ _ _ i w e _ => (e.ch = none → pagePosAt B n i w.pgid) →
      e.D.Nodup ∧ ∀ s ∈ e.D, Pc X.v B (· ∈ e.N) (fun l k => l ∈ e.N ∨ (l = n ∧ k = i)) s)
    (fun n r _ _ Sb hnode huN hleaf _ _ hsb0 => by
      have hr := node_ns hc hnode
      have hz : (List.range r.ws.length).flatMap (fun i => pgSlots X.v.pages (Sb i)) = [] := by
        rw [List.flatMap_eq_nil_iff]
        intro i hi
        rw [List.mem_range] at hi
        rw [hsb0 i r.ws[i] (List.getElem?_eq_getElem hi) (hnb n r hr hleaf _ (List.getElem_mem hi))]
        rfl
      rw [hz, List.append_nil]
      obtain ⟨hnd, hp⟩ := ownSl_pc hr huN.2.2.2.2.2.2.2
      exact ⟨hnd, fun s hs => Pc_mono (fun l hl => by rw [hl]; exact List.mem_singleton_self _)
        (fun _ _ h => h.elim) (hp s hs)⟩)
    (fun n r _ _ _ es hnode huN hleaf _ hlen hent _ hcsE _ hNnd _ ih => by
      have hr := node_ns hc hnode
      have hE : ∀ (i : Nat) (e : UE), es[i]? = some e → e.D.Nodup ∧
          ∀ s ∈ e.D, Pc X.v B (· ∈ e.N) (fun l k => l ∈ e.N ∨ (l = n ∧ k = i)) s := by
        intro i e he
        have hi : i < r.ws.length := by have := (List.getElem?_eq_some_iff.1 he).1; omega
        have hw : r.ws[i]? = some r.ws[i] := List.getElem?_eq_getElem hi
        exact ih i _ e hw he (fun hch =>
          ⟨r, r.ws[i], hr, hleaf, hw, rfl, fin_unmat hcl hc hr hleaf hlen hent hcsE hw he hch⟩)
      have hNf : (es.flatMap UE.N).Nodup := (List.nodup_cons.1 hNnd).2
      have hnN : n ∉ es.flatMap UE.N := (List.nodup_cons.1 hNnd).1
      have hnotn : ∀ (i : Nat) (e : UE), es[i]? = some e → n ∉ e.N := fun i e he hn =>
        hnN (List.mem_flatMap.2 ⟨e, List.mem_of_getElem? he, hn⟩)
      have hfl : (es.flatMap UE.D).Nodup :=
        Pc_nodup_flatMap hcl hpd UE.D (fun _ e => (· ∈ e.N))
          (fun i e l k => l ∈ e.N ∨ (l = n ∧ k = i)) es
          (fun a ha => by
            obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
            exact (hE i _ (List.getElem?_eq_getElem hi)).1)
          (fun i a ha s hs => (hE i a ha).2 s hs)
          (fun i j a b hij ha hb x hxa hxb =>
            flatMap_nodup_disj UE.N es i j a b x hNf hij ha hb hxa hxb)
          (fun i j a b hij ha hb x k hxa hxb => by
            rcases hxa with hxa | ⟨rfl, rfl⟩ <;> rcases hxb with hxb | ⟨hxn, hk⟩
            · exact flatMap_nodup_disj UE.N es i j a b x hNf hij ha hb hxa hxb
            · subst hxn; exact hnotn i a ha hxa
            · exact hnotn j b hb hxb
            · omega)
      obtain ⟨hond, hop⟩ := ownSl_pc hr huN.2.2.2.2.2.2.2
      refine ⟨List.nodup_append.2 ⟨hond, hfl, ?_⟩, ?_⟩
      · intro x hx y hy hxy
        subst hxy
        obtain ⟨e, hem, hxe⟩ := List.mem_flatMap.1 hy
        obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hem
        have hej : es[j]? = some es[j] := List.getElem?_eq_getElem hj
        exact Pc_disj hcl hpd (fun l h1 h2 => by subst h1; exact hnotn j _ hej h2)
          (fun _ _ h _ => h) (hop x hx) ((hE j _ hej).2 x hxe)
      · intro s hs
        rcases List.mem_append.1 hs with hs | hs
        · exact Pc_mono (fun l hl => by subst hl; exact List.mem_cons_self) (fun _ _ h => h.elim)
            (hop s hs)
        · obtain ⟨e, hem, hse⟩ := List.mem_flatMap.1 hs
          obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hem
          have hej : es[j]? = some es[j] := List.getElem?_eq_getElem hj
          have hmem : ∀ l, l ∈ es[j].N → l ∈ n :: es.flatMap UE.N := fun l hl =>
            List.mem_cons_of_mem _ (List.mem_flatMap.2 ⟨_, hem, hl⟩)
          refine Pc_mono hmem (fun l k hl => ?_) ((hE j _ hej).2 s hse)
          rcases hl with hl | ⟨rfl, -⟩
          · exact hmem l hl
          · exact List.mem_cons_self)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih => fun _ =>
      ⟨ih.1, fun s hs => Pc_mono (fun l hl => hl) (fun l k hl => Or.inl hl) (ih.2 s hs)⟩)
    (fun n _ _ _ _ _ i w S _ hfT hpp => by
      have hpp := hpp rfl
      have hs := hfT.1
      have hP : ∀ x ∈ S, (X.v.pages !! x).isSome := fun x hx => by
        obtain ⟨pg, hpg⟩ := treeHas_page ((hs.has x).2 hx); rw [hpg]; rfl
      refine ⟨pgSlots_nodup hpd hs.nodup hP, fun s' hs' => ?_⟩
      obtain ⟨x, hx, pg, hpg, h1, h2⟩ := mem_pgSlots hP hs'
      exact ⟨x, pg, hpg, h1, h2, Or.inr ⟨n, i, w.pgid, Or.inr ⟨rfl, rfl⟩, hpp, (hs.has x).2 hx⟩⟩)
    hu

end cov

end Spill

end bbolt
end EtcdGrove
end Perennial

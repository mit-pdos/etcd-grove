/-
`Bucket.spill`'s root loop's end (U9x9, `notes/bbolt-proof-plan.md`): **the root bucket's
unspilled tree's slots are distinct pieces** (`uTree_piecesE`: `BktSlotCov.uTree_pieces` with
nested buckets). Every slot `D` of an unspilled tree whose positions are the walk's (`t`, its
finite logical tree) is labelled (`labL`): a slot of an owner's view page (a node's page, or an
own page under a page position; `Pc`), covered by a position of the walk (`coverW`), or a slot of
the nested bucket of one of its elements (`entL`: a leaf node's `bvalS` slots, or a nested page
of a finished subtree's leaf page). Two pieces' slots are distinct: two owners' by `Pc_disj`, an
owner's and an element's, or two elements' of distinct keys, by the global facts `GDisj` (proved
from the loop's invariant, `BktEndDisj`). The elements' keys are distinct (`BktEndKeys`).
-/
module

public import Proof.go_etcd_io.bbolt.Spill.BktEndNilPos
public import Proof.go_etcd_io.bbolt.Spill.BktEndCov
public import Proof.go_etcd_io.bbolt.Spill.BktEndShape
public import Proof.go_etcd_io.bbolt.Txn.WInit
public import Proof.go_etcd_io.bbolt.Spill.BktValKey

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove
namespace bbolt

open go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

namespace Spill

section pieces
variable [GooseExts]

theorem pgSlots_nodup_disj {P : Pages} {S : List Nat} (hS : S.Nodup)
    (hP : ∀ x ∈ S, (P !! x).isSome)
    (hd : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → ∀ pgx pgy, P !! x = some pgx → P !! y = some pgy →
      extDisj x pgx y pgy) : (pgSlots P S).Nodup := by
  unfold pgSlots
  refine nodup_flatMap_of' _ S (fun x _ => ?_) ?_
  · cases P !! x with
    | some pg => exact List.nodup_range'
    | none => simp
  · intro i j a b x hij ha hb hxa hxb
    have hne : a ≠ b := by
      intro e; subst e
      have := nodup_idx' hS ha hb; omega
    have ha' := List.mem_of_getElem? ha
    have hb' := List.mem_of_getElem? hb
    obtain ⟨pga, hpa⟩ := Option.isSome_iff_exists.1 (hP a ha')
    obtain ⟨pgb, hpb⟩ := Option.isSome_iff_exists.1 (hP b hb')
    rw [hpa] at hxa; rw [hpb] at hxb
    simp only [List.mem_range'] at hxa hxb
    rcases hd a ha' b hb' hne pga pgb hpa hpb with h | h <;> omega

theorem sTree_isSome {P : Pages} {hwm id : Nat} {lo hi : Option (List w8)} {h : Nat}
    {S : List Nat} (hs : sTree P hwm id lo hi h S) : ∀ x ∈ S, (P !! x).isSome := fun x hx => by
  obtain ⟨pg, hpg⟩ := treeHas_page ((hs.has x).2 hx); rw [hpg]; rfl

theorem sTree_pgSlots_nodup {P : Pages} {hwm id : Nat} {lo hi : Option (List w8)} {h : Nat}
    {S : List Nat} (hs : sTree P hwm id lo hi h S) : (pgSlots P S).Nodup :=
  pgSlots_nodup_disj hs.nodup (sTree_isSome hs) hs.disj

/-- A nested value's slots are distinct, and covered by its tree. -/
theorem bvalS_slots {P : Pages} {hwm : Nat} {v : List w8} {S : List Nat} (hb : bvalS P hwm v S) :
    (pgSlots P S).Nodup ∧ ∀ s ∈ pgSlots P S, bucketCovers P v s := by
  rcases hb.2 with ⟨-, hS, -⟩ | ⟨-, h, hs⟩
  · subst hS; exact ⟨by simp [pgSlots], fun s hs => by simp [pgSlots] at hs⟩
  · refine ⟨sTree_pgSlots_nodup hs, fun s hsl => ?_⟩
    obtain ⟨x, hx, pg, hpg, h1, h2⟩ := mem_pgSlots (sTree_isSome hs) hsl
    exact ⟨x, pg, (bvalS_has hb x).2 hx, hpg, h1, h2⟩

/-- A position without a node reads its page. -/
theorem ltree_unres {X : WX} {bl : Loc} {B : BRec} (hB : X.t.bs !! bl = some B)
    (h0 : B.ib.root' ≠ W64 0) {p : w64} (hr : resolve B p = none) {pg : List w8}
    (hpg : X.v.pages !! p.toNat = some pg) :
    ltree X bl p = some (decide (pageFlags pg = leafPageFlag), pageWs pg) := by
  unfold ltree; rw [hB]; simp only; rw [hr]
  unfold wpageAt; rw [if_neg h0, hpg]; rfl

/-- **A page position's extent covers its page's slots.** -/
theorem coverW_unres {X : WX} {bl : Loc} {B : BRec} (hB : X.t.bs !! bl = some B)
    (h0 : B.ib.root' ≠ W64 0) {d : Nat} (h2 : 2 ≤ d) (h64 : d < 2 ^ 64)
    (hr : resolve B (W64 (d : Int)) = none) (hp : W64 (d : Int) ∈ X.positions bl)
    {pg : List w8} (hpg : X.v.pages !! d = some pg) {s : Nat} (h1 : d ≤ s)
    (h3 : s < d + (1 + pageOverflow pg)) : coverW X s (.pos bl (W64 (d : Int))) := by
  have hdn : (W64 (d : Int)).toNat = d := w64_cast_toNat h64
  have hne : W64 (d : Int) ≠ W64 0 := by
    intro e; have := congrArg BitVec.toNat e; rw [hdn] at this; simp at this; omega
  refine ⟨by rw [hB]; simp, hp, (W64 (d : Int), 1 + pageOverflow pg), ?_,
    by rw [hdn]; exact h1, by rw [hdn]; exact h3⟩
  unfold WX.posExtent; rw [hB]; simp only; rw [hr]; simp only
  rw [if_neg hne, hdn, hpg]; rfl

/-- **A node's position's extent covers its page's slots.** -/
theorem coverW_ownSl {X : WX} {bl : Loc} {B : BRec} (hB : X.t.bs !! bl = some B) {pid : w64}
    {n : Loc} {r : NRec} (hres : resolve B pid = some n) (hr : B.ns !! n = some r)
    (hown : ownPg X.v r.nv.pgid') (hp : pid ∈ X.positions bl) {s : Nat}
    (hs : s ∈ ownSl X.v r.nv.pgid') : coverW X s (.pos bl pid) := by
  unfold ownSl at hs
  split at hs
  · cases hs
  · rename_i h0
    unfold pgSlots at hs
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil] at hs
    cases hpg : X.v.pages !! r.nv.pgid'.toNat with
    | none =>
      obtain ⟨pg, hpg', -⟩ := hown h0
      rw [hpg] at hpg'; cases hpg'
    | some pg =>
      rw [hpg] at hs
      simp only [List.mem_range'] at hs
      obtain ⟨k, hk, rfl⟩ := hs
      refine ⟨by rw [hB]; simp, hp, (r.nv.pgid', 1 + pageOverflow pg), ?_, by simp only; omega,
        by simp only; omega⟩
      unfold WX.posExtent; rw [hB]; simp only; rw [hres]; simp only [hr, Option.map_some,
        Option.getD_some]
      rw [if_neg h0, hpg]; rfl

/-- A slot of the nested bucket of one of the elements `E`. -/
def entL (P : Pages) (E : List El) (s : Nat) : Prop :=
  ∃ e ∈ E, e.1 % 2 = 1 ∧ bucketCovers P e.2.2 s

/-- **A piece's slot** (see the module doc). -/
def labL (X : WX) (bl : Loc) (B : BRec) (P : Pages) (NS : Loc → Prop) (PS : Loc → Nat → Prop)
    (E : List El) (s : Nat) : Prop :=
  (Pc X.v B NS PS s ∧ ∃ q, coverW X s (.pos bl q)) ∨ entL P E s

/-- **The global disjointness the pieces need**: a slot a position covers is no element's nested
bucket's, nor two elements' of distinct keys. -/
structure GDisj (X : WX) (bl : Loc) (P : Pages) (E0 : List El) : Prop where
  oe : ∀ s q e, coverW X s (.pos bl q) → e ∈ E0 → e.1 % 2 = 1 → bucketCovers P e.2.2 s → False
  ee : ∀ s e e', e ∈ E0 → e' ∈ E0 → e.2.1 ≠ e'.2.1 → e.1 % 2 = 1 → e'.1 % 2 = 1 →
    bucketCovers P e.2.2 s → bucketCovers P e'.2.2 s → False

theorem labL_mono {X : WX} {bl : Loc} {B : BRec} {P : Pages} {NS NS' : Loc → Prop}
    {PS PS' : Loc → Nat → Prop} {E E' : List El} (hN : ∀ l, NS l → NS' l)
    (hP : ∀ l k, PS l k → PS' l k) (hE : ∀ e ∈ E, e ∈ E') {s : Nat}
    (h : labL X bl B P NS PS E s) : labL X bl B P NS' PS' E' s := by
  rcases h with ⟨hp, hq⟩ | ⟨e, he, h1, h2⟩
  · exact Or.inl ⟨Pc_mono hN hP hp, hq⟩
  · exact Or.inr ⟨e, hE e he, h1, h2⟩

/-- **Two pieces of disjoint owners and elements of distinct keys share no slot.** -/
theorem labL_disj {X : WX} {bl : Loc} {B : BRec} {hwm : Nat} (hcl : bktClean X.v hwm bl B)
    (hpd : pagesDisjoint X.v.pages) {P : Pages} {E0 : List El} (hg : GDisj X bl P E0)
    {NS1 NS2 : Loc → Prop} {PS1 PS2 : Loc → Nat → Prop} {E1 E2 : List El}
    (hN : ∀ l, NS1 l → NS2 l → False) (hP : ∀ l k, PS1 l k → PS2 l k → False)
    (hE1 : ∀ e ∈ E1, e ∈ E0) (hE2 : ∀ e ∈ E2, e ∈ E0)
    (hE : ∀ e ∈ E1, ∀ e' ∈ E2, e.2.1 ≠ e'.2.1) {s : Nat}
    (h1 : labL X bl B P NS1 PS1 E1 s) (h2 : labL X bl B P NS2 PS2 E2 s) : False := by
  rcases h1 with ⟨p1, q1, hq1⟩ | ⟨e, he, hb, hc⟩ <;>
    rcases h2 with ⟨p2, q2, hq2⟩ | ⟨e', he', hb', hc'⟩
  · exact Pc_disj hcl hpd hN hP p1 p2
  · exact hg.oe s q1 e' hq1 (hE2 e' he') hb' hc'
  · exact hg.oe s q2 e hq2 (hE1 e he) hb hc
  · exact hg.ee s e e' (hE1 e he) (hE2 e' he') (hE e he e' he') hb hb' hc hc'

/-- The keys of a list's elements, pairwise distinct. -/
abbrev keysNe (E : List El) : Prop := E.Pairwise fun a b => a.2.1 ≠ b.2.1

theorem keysNe_get {E : List El} (h : keysNe E) {i j : Nat} (hij : i < j) (hj : j < E.length) :
    E[i].2.1 ≠ E[j].2.1 :=
  List.pairwise_iff_getElem.1 h i j (by omega) hj hij

/-- **The pieces of an unspilled tree** (see the module doc). -/
theorem uTree_piecesE {X : WX} {bl : Loc} {B : BRec} {hwm' : Nat} (hB : X.t.bs !! bl = some B)
    (hcl : bktClean X.v hwm' bl B) (h0 : B.ib.root' ≠ W64 0) (hpd : pagesDisjoint X.v.pages)
    (h64 : ∀ x pg, X.v.pages !! x = some pg → x < 2 ^ 64)
    {P : Pages} (hag : pagesLe X.v.pages P) {E0 : List El} (hg : GDisj X bl P E0)
    {t : RTree} (ht : ltIs (ltree X) bl t) (hpos : X.positions bl = t.pos)
    {hwm : Nat} {n : Loc} {lo hi : Option (List w8)} {h : Nat} {F D : List Nat} {N : List Loc}
    {E : List El} (hu : uTree X bl P hwm n lo hi h F D N E) :
    (∀ e ∈ E, e ∈ E0) → keysNe E → ∀ pid, resolve B pid = some n → pid ∈ t.pos →
      D.Nodup ∧ ∀ s ∈ D, labL X bl B P (· ∈ N) (fun l _ => l ∈ N) E s :=
  uTree.rec (X := X) (bl := bl) (P := P) (hwm := hwm)
    (motive_1 := fun n _ _ _ _ D N E _ => (∀ e ∈ E, e ∈ E0) → keysNe E → ∀ pid,
      resolve B pid = some n → pid ∈ t.pos →
      D.Nodup ∧ ∀ s ∈ D, labL X bl B P (· ∈ N) (fun l _ => l ∈ N) E s)
    (motive_2 := fun n _ _ _ _ _ i w e _ => (e.ch = none → pagePosAt B n i w.pgid) →
      (∀ x ∈ e.E, x ∈ E0) → keysNe e.E → w.pgid ∈ t.pos →
      e.D.Nodup ∧ ∀ s ∈ e.D, labL X bl B P (· ∈ e.N) (fun l k => l ∈ e.N ∨ (l = n ∧ k = i)) e.E s)
    (fun n r _ _ Sb hnode huN _ _ hsb hsb0 => by
      intro hE0 hkn pid hres hpt
      have hr := node_ns hB hnode
      have hpt' : pid ∈ X.positions bl := by rw [hpos]; exact hpt
      obtain ⟨hond, hop⟩ := ownSl_pc hr huN.2.2.2.2.2.2.2
      have hown : ∀ s ∈ ownSl X.v r.nv.pgid',
          labL X bl B P (· ∈ [n]) (fun l _ => l ∈ [n]) (r.ws.map wEl) s := fun s hs =>
        Or.inl ⟨Pc_mono (fun l hl => by rw [hl]; exact List.mem_singleton_self _)
          (fun _ _ h => h.elim) (hop s hs), pid, coverW_ownSl hB hres hr huN.2.2.2.2.2.2.2 hpt' hs⟩
      have hsbi : ∀ i (hi : i < r.ws.length), (pgSlots P (Sb i)).Nodup ∧
          ∀ s ∈ pgSlots P (Sb i), entL P [wEl r.ws[i]] s := by
        intro i hi
        by_cases hbk : isBktFlag r.ws[i].flags
        · obtain ⟨hnd, hcov⟩ := bvalS_slots (hsb i _ (List.getElem?_eq_getElem hi) hbk)
          exact ⟨hnd, fun s hs => ⟨wEl r.ws[i], List.mem_singleton_self _,
            (isBkt_iff _).1 hbk, hcov s hs⟩⟩
        · rw [hsb0 i _ (List.getElem?_eq_getElem hi) hbk]
          exact ⟨by simp [pgSlots], fun s hs => by simp [pgSlots] at hs⟩
      have hEl : ∀ i (hi : i < r.ws.length), wEl r.ws[i] ∈ r.ws.map wEl := fun i hi =>
        List.mem_map_of_mem (List.getElem_mem hi)
      have hfl : ((List.range r.ws.length).flatMap fun i => pgSlots P (Sb i)).Nodup := by
        refine nodup_flatMap_of' _ _ (fun a ha => (hsbi a (List.mem_range.1 ha)).1) ?_
        intro i j a b x hij ha hb hxa hxb
        have hj : j < r.ws.length := by
          have := (List.getElem?_eq_some_iff.1 hb).1; simpa using this
        rw [List.getElem?_range (by omega)] at ha hb
        cases ha; cases hb
        obtain ⟨e, he, hb1, hc1⟩ := (hsbi i (by omega)).2 x hxa
        obtain ⟨e', he', hb2, hc2⟩ := (hsbi j hj).2 x hxb
        rw [List.mem_singleton] at he he'; subst he; subst he'
        refine hg.ee x _ _ (hE0 _ (hEl i (by omega))) (hE0 _ (hEl j hj)) ?_ hb1 hb2 hc1 hc2
        have := keysNe_get hkn (i := i) (j := j) hij (by simpa using hj)
        simpa using this
      have hsb' : ∀ s ∈ (List.range r.ws.length).flatMap (fun i => pgSlots P (Sb i)),
          entL P (r.ws.map wEl) s := by
        intro s hs
        obtain ⟨i, hi, hs⟩ := List.mem_flatMap.1 hs
        rw [List.mem_range] at hi
        obtain ⟨e, he, h1, h2⟩ := (hsbi i hi).2 s hs
        rw [List.mem_singleton] at he; subst he
        exact ⟨_, hEl i hi, h1, h2⟩
      refine ⟨List.nodup_append.2 ⟨hond, hfl, ?_⟩, fun s hs => ?_⟩
      · intro x hx y hy hxy
        subst hxy
        obtain ⟨e, he, hb, hc⟩ := hsb' x hy
        exact hg.oe x pid e (coverW_ownSl hB hres hr huN.2.2.2.2.2.2.2 hpt' hx) (hE0 e he) hb hc
      · rcases List.mem_append.1 hs with hs | hs
        · exact hown s hs
        · exact Or.inr (hsb' s hs))
    (fun n r _ _ _ es hnode huN hleaf _ hlen hent _ hcsE _ hNnd _ ih => by
      intro hE0 hkn pid hres hpt
      have hr := node_ns hB hnode
      have hpt' : pid ∈ X.positions bl := by rw [hpos]; exact hpt
      have hL : ltree X bl pid = some (false, r.ws) := by
        simp only [ltree, hB, hres, hr, Option.map_some, hleaf]
      unfold keysNe at hkn
      rw [List.pairwise_flatMap] at hkn
      obtain ⟨hknE, hknX⟩ := hkn
      have hE : ∀ (i : Nat) (e : UE), es[i]? = some e → e.D.Nodup ∧
          ∀ s ∈ e.D, labL X bl B P (· ∈ e.N) (fun l k => l ∈ e.N ∨ (l = n ∧ k = i)) e.E s := by
        intro i e he
        have hi : i < r.ws.length := by have := (List.getElem?_eq_some_iff.1 he).1; omega
        have hw : r.ws[i]? = some r.ws[i] := List.getElem?_eq_getElem hi
        have hem := List.mem_of_getElem? he
        exact ih i _ e hw he (fun hch =>
          ⟨r, r.ws[i], hr, hleaf, hw, rfl, fin_unmat hcl hB hr hleaf hlen hent hcsE hw he hch⟩)
          (fun x hx => hE0 x (List.mem_flatMap.2 ⟨e, hem, hx⟩)) (hknE e hem)
          (pos_child ht hpt hL hi)
      have hNf : (es.flatMap UE.N).Nodup := (List.nodup_cons.1 hNnd).2
      have hnN : n ∉ es.flatMap UE.N := (List.nodup_cons.1 hNnd).1
      have hnotn : ∀ (i : Nat) (e : UE), es[i]? = some e → n ∉ e.N := fun i e he hn =>
        hnN (List.mem_flatMap.2 ⟨e, List.mem_of_getElem? he, hn⟩)
      have hEsub : ∀ (i : Nat) (e : UE), es[i]? = some e → ∀ x ∈ e.E, x ∈ E0 :=
        fun i e he x hx => hE0 x (List.mem_flatMap.2 ⟨e, List.mem_of_getElem? he, hx⟩)
      have hfl : (es.flatMap UE.D).Nodup := by
        refine nodup_flatMap_of' UE.D es (fun a ha => ?_) ?_
        · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
          exact (hE i _ (List.getElem?_eq_getElem hi)).1
        · intro i j a b x hij ha hb hxa hxb
          refine labL_disj hcl hpd hg (NS1 := (· ∈ a.N)) (NS2 := (· ∈ b.N))
            (PS1 := fun l k => l ∈ a.N ∨ (l = n ∧ k = i))
            (PS2 := fun l k => l ∈ b.N ∨ (l = n ∧ k = j))
            (fun x hxa hxb => flatMap_nodup_disj UE.N es i j a b x hNf hij ha hb hxa hxb)
            (fun x k hxa hxb => by
              rcases hxa with hxa | ⟨rfl, rfl⟩ <;> rcases hxb with hxb | ⟨hxn, hk⟩
              · exact flatMap_nodup_disj UE.N es i j a b x hNf hij ha hb hxa hxb
              · subst hxn; exact hnotn i a ha hxa
              · exact hnotn j b hb hxb
              · omega)
            (hEsub i a ha) (hEsub j b hb) (fun e he e' he' => ?_)
            ((hE i a ha).2 x hxa) ((hE j b hb).2 x hxb)
          have hj : j < es.length := (List.getElem?_eq_some_iff.1 hb).1
          have := List.pairwise_iff_getElem.1 hknX i j (by omega) hj hij
          rw [(List.getElem?_eq_some_iff.1 ha).2] at this
          rw [(List.getElem?_eq_some_iff.1 hb).2] at this
          exact this e he e' he'
      obtain ⟨hond, hop⟩ := ownSl_pc hr huN.2.2.2.2.2.2.2
      have hown : ∀ s ∈ ownSl X.v r.nv.pgid',
          labL X bl B P (· = n) (fun _ _ => False) [] s := fun s hs =>
        Or.inl ⟨hop s hs, pid, coverW_ownSl hB hres hr huN.2.2.2.2.2.2.2 hpt' hs⟩
      refine ⟨List.nodup_append.2 ⟨hond, hfl, ?_⟩, ?_⟩
      · intro x hx y hy hxy
        subst hxy
        obtain ⟨e, hem, hxe⟩ := List.mem_flatMap.1 hy
        obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hem
        have hej : es[j]? = some es[j] := List.getElem?_eq_getElem hj
        exact labL_disj hcl hpd hg (fun l h1 h2 => by subst h1; exact hnotn j _ hej h2)
          (fun _ _ h _ => h) (fun _ h => by cases h) (hEsub j _ hej) (fun _ h => by cases h)
          (hown x hx) ((hE j _ hej).2 x hxe)
      · intro s hs
        rcases List.mem_append.1 hs with hs | hs
        · exact labL_mono (fun l hl => by subst hl; exact List.mem_cons_self)
            (fun _ _ h => h.elim) (fun _ h => by cases h) (hown s hs)
        · obtain ⟨e, hem, hse⟩ := List.mem_flatMap.1 hs
          obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hem
          have hej : es[j]? = some es[j] := List.getElem?_eq_getElem hj
          have hmem : ∀ l, l ∈ es[j].N → l ∈ n :: es.flatMap UE.N := fun l hl =>
            List.mem_cons_of_mem _ (List.mem_flatMap.2 ⟨_, hem, hl⟩)
          refine labL_mono hmem (fun l k hl => ?_)
            (fun x hx => List.mem_flatMap.2 ⟨_, hem, hx⟩) ((hE j _ hej).2 s hse)
          rcases hl with hl | ⟨rfl, -⟩
          · exact hmem l hl
          · exact List.mem_cons_self)
    (fun _ _ _ _ _ _ _ w c rc _ _ _ _ _ hnode _ hpg _ _ _ _ ih => by
      intro _ hE0 hkn hpt
      have hr := node_ns hB hnode
      have hnm : B.nm !! rc.nv.pgid' = some c := (hcl.2.2.2.2.2.2.2.1 c rc hr).2.2.2.2.2.2.2.1
      rw [hpg] at hnm
      have hres : resolve B w.pgid = some c := by unfold resolve; rw [if_neg h0]; exact hnm
      obtain ⟨hnd, hl⟩ := ih hE0 hkn w.pgid hres hpt
      exact ⟨hnd, fun s hs => labL_mono (fun l hl => hl) (fun l k hl => Or.inl hl)
        (fun x hx => hx) (hl s hs)⟩)
    (fun n _ _ _ _ _ i w S E hfT => by
      intro hpp hE0 _ hpt
      have hpp := hpp rfl
      have hpr : posRoot B w.pgid.toNat :=
        Or.inr ⟨n, i, by rw [w64_toNat_cast]; exact hpp, w.pgid.isLt⟩
      have hwf := posRoot_treeWF hcl hpr
      have hs := hfT.1
      refine ⟨sTree_pgSlots_nodup hs, fun s hsl => ?_⟩
      obtain ⟨x, hx, pg, hpg, h1, h2⟩ := mem_pgSlots (sTree_isSome hs) hsl
      have hxv : treeHas X.v.pages w.pgid.toNat x :=
        treeHas_of_le hag hwm' ((hs.has x).2 hx) hwf
      obtain ⟨pgv, hpgv⟩ := treeHas_page hxv
      have e1 := hag x pgv hpgv
      rw [hpg] at e1; cases e1
      rcases treeHas_split X.v.pages hxv with hown |
        ⟨L, pgL, j, hoL, hpL, hlf, hj, hbf, hbh⟩
      · -- an own page of the page position: a position of the walk
        have hfree : ∀ d, treeHas X.v.pages w.pgid.toNat d → B.nm !! W64 (d : Int) = none :=
          fun d hd => hcl.2.2.2.2.2.2.2.2.2.1 n i w.pgid hpp d hd
        have hxpos : W64 (x : Int) ∈ t.pos := pos_own ht hown w.pgid rfl hpt
          (fun y pgy ho hy => ltree_unres hB h0 (by
            unfold resolve; rw [if_neg h0]
            have := hfree y.toNat (treeHas_of_ownHas ho); rwa [Write.w64_toNat_eq] at this) hy)
        have hwfx := Read.treeHas_treeWF X.v.pages hwm' hxv hwf
        have h2x : 2 ≤ x := by cases hwfx with | page _ _ h _ _ _ _ _ => exact h
        have hrx : resolve B (W64 (x : Int)) = none := by
          unfold resolve; rw [if_neg h0]; exact hfree x hxv
        refine Or.inl ⟨⟨x, pg, hpgv, h1, h2, Or.inr ⟨n, i, w.pgid, Or.inr ⟨rfl, rfl⟩, hpp, hxv⟩⟩,
          W64 (x : Int), coverW_unres hB h0 h2x (h64 x pg hpgv) hrx (by rw [hpos]; exact hxpos)
            hpgv h1 h2⟩
      · -- a page of a nested bucket of one of its leaves' elements
        refine Or.inr ⟨(leafFlags pgL j, leafKey pgL j, leafValue pgL j), ?_, hbf, x, pg,
          bucketHas_le hag hbh, hag x pg hpgv, h1, h2⟩
        rw [← hfT.2.2]
        have hlv := ownLeaf_mem_treeLeaves hs (ownHas_le hag hoL) (hag L pgL hpL) hlf
        unfold treeEls
        exact List.mem_flatMap.2 ⟨pgL, hlv, List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩⟩)
    hu

end pieces

end Spill

end bbolt
end EtcdGrove
end Perennial

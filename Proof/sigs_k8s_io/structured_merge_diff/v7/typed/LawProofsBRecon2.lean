/-
Pure helpers of the reconcile walker's `visitListItems`/`visitMapItems` (`reconcileWithSchemaWalker`):
`reconBelow` at a granular node is the union (`optU`) of its children's `reconOut` (`reconKid`),
over any list of path elements covering the set's children (`reconKids_eq`); a child's set
(`PathSet.under`) counts at most the parent's.
-/
module

public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.LawProofsBRecon
public import Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.LawProofsCard
import all Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Defs

@[expose] public section

noncomputable section

set_option linter.unusedSimpArgs false

namespace Perennial
namespace EtcdGrove
namespace smd

open Iris Iris.BI Iris.ProofMode
open sigs_k8s_io.structured_merge_diff.v7

namespace LawBR

/-! ## A child's set -/

theorem deep_heads (F : PathSet) : F.deep.heads = F.heads := by
  apply FSet.ext'; intro x
  rw [PathSet_mem_heads_law_holds, PathSet_mem_heads_law_holds]
  constructor
  · rintro ⟨q, hq, h⟩; exact ⟨q, hq, ((PathSet_mem_deep_law_holds _ _).1 h).1⟩
  · rintro ⟨q, hq, h⟩
    refine ⟨q, hq, (PathSet_mem_deep_law_holds _ _).2 ⟨h, ?_⟩⟩
    cases q with
    | nil => exact absurd rfl hq
    | cons _ _ => simp

theorem deep_under (F : PathSet) (x : PE) : F.deep.under x = F.under x := by
  apply FSet.ext'; intro q
  rw [PathSet_mem_under_law_holds, PathSet_mem_under_law_holds]
  constructor
  · rintro ⟨hq, h⟩; exact ⟨hq, ((PathSet_mem_deep_law_holds _ _).1 h).1⟩
  · rintro ⟨hq, h⟩
    refine ⟨hq, (PathSet_mem_deep_law_holds _ _).2 ⟨h, ?_⟩⟩
    cases q with
    | nil => exact absurd rfl hq
    | cons _ _ => simp

theorem under_empty (F : PathSet) (x : PE) (h : x ∉ F.heads) : F.under x = PathSet.empty := by
  apply FSet.ext'; intro q
  rw [PathSet_mem_under_law_holds]
  constructor
  · rintro ⟨hq, hm⟩; exact absurd ((PathSet_mem_heads_law_holds _ _).2 ⟨q, hq, hm⟩) h
  · intro hm; exact absurd hm (FSet.mem_empty q)

/-- A child's set counts at most its parent's. -/
theorem under_cardLt (F : PathSet) (x : PE) (n : Nat) (h : F.CardLt n) : (F.under x).CardLt n := by
  unfold FSet.CardLt at *
  rw [← fpK.card_cons_map x]
  refine Nat.lt_of_le_of_lt (FSet.card_le_of_subset _ _ ?_) h
  intro q hq
  rw [FSet.mem_map'] at hq
  obtain ⟨r, hr, rfl⟩ := hq
  exact ((PathSet_mem_under_law_holds _ _ _).1 hr).2

/-! ## Optional sets that are `none` exactly when empty -/

/-- `none` for the empty set, else the set. -/
def toO (s : PathSet) : Option PathSet := if s.isEmpty then none else some s

theorem toO_congr {a b : PathSet} (h : ∀ q, q ∈ a ↔ q ∈ b) : toO a = toO b := by
  rw [FSet.ext' h]

theorem union_isEmpty (a b : PathSet) :
    (FSet.union a b).isEmpty = (a.isEmpty && b.isEmpty) := by
  apply Bool.eq_iff_iff.2
  rw [Bool.and_eq_true, FSet.isEmpty_iff', FSet.isEmpty_iff', FSet.isEmpty_iff']
  constructor
  · intro h; exact ⟨fun x hx => h x ((FSet.mem_union' _ _ _).2 (Or.inl hx)),
      fun x hx => h x ((FSet.mem_union' _ _ _).2 (Or.inr hx))⟩
  · rintro ⟨h1, h2⟩ x hx
    rcases (FSet.mem_union' _ _ _).1 hx with hx | hx
    · exact h1 x hx
    · exact h2 x hx

theorem optU_toO (a b : PathSet) : optU (toO a) (toO b) = toO (PathSet.union a b) := by
  unfold toO PathSet.union
  rw [union_isEmpty]
  cases ha : a.isEmpty <;> cases hb : b.isEmpty
  · rfl
  · simp only [Bool.false_eq_true, ↓reduceIte, Bool.and_true]
    rw [fset_isEmpty_eq b hb, LawB.fset_union_empty]
    rfl
  · simp only [Bool.false_eq_true, ↓reduceIte, Bool.true_and]
    rw [fset_isEmpty_eq a ha, LawB.fset_empty_union]
    rfl
  · rfl
where
  fset_isEmpty_eq := @LawB.fset_isEmpty_eq

theorem toO_empty : toO PathSet.empty = none := rfl

theorem map_isEmpty (f : Path → Path) (s : PathSet) : (s.map f).isEmpty = s.isEmpty := by
  apply Bool.eq_iff_iff.2
  rw [FSet.isEmpty_iff', FSet.isEmpty_iff']
  constructor
  · intro h x hx; exact h (f x) ((FSet.mem_map' _ _ _).2 ⟨x, hx, rfl⟩)
  · intro h y hy
    obtain ⟨x, hx, -⟩ := (FSet.mem_map' _ _ _).1 hy
    exact h x hx

theorem reconBelow_toO (S : Schema) (t : TypeRef) (p : Path) (F : PathSet) :
    reconBelow S t p F = toO ((atomicNodes S t F).map (p ++ ·)) := by
  unfold reconBelow toO
  rw [map_isEmpty]

/-- What a node adds (`reconOut`), as a set. -/
def outS (S : Schema) (t : TypeRef) (p : Path) (b : Bool) (F : PathSet) : PathSet :=
  PathSet.union (if reconTouch S t b F then ins p else PathSet.empty)
    ((atomicNodes S t F).map (p ++ ·))

theorem ins_isEmpty (p : Path) (h : p ≠ []) : (ins p).isEmpty = false := by
  cases p with
  | nil => exact absurd rfl h
  | cons _ _ => rfl

theorem reconOut_toO (S : Schema) (t : TypeRef) (p : Path) (b : Bool) (F : PathSet) (hp : p ≠ []) :
    reconOut S t p b F = toO (outS S t p b F) := by
  unfold reconOut toO outS PathSet.union
  rw [union_isEmpty, map_isEmpty]
  cases hT : reconTouch S t b F <;> cases hn : (atomicNodes S t F).isEmpty
  · simp [hn]
  · dsimp only; rw [hn]; rfl
  · simp [ins_isEmpty p hp]
  · simp [ins_isEmpty p hp]

/-! ## The children's `reconOut` -/

/-- **The child at `x`'s contribution** (`visitListItems`/`visitMapItems`' `handleElement`): the
child's `reconOut` at its type (none if the schema has none for it), reached as a member without
children exactly when it has none, with its child set. -/
def reconKid (S : Schema) (t : TypeRef) (p : Path) (F : PathSet) (x : PE) : Option PathSet :=
  match reconChild S t x with
  | some t' => reconOut S t' (p ++ [x]) (decide (x ∉ F.heads)) (F.under x)
  | none => none

/-- The children's contributions over `L`, in order. -/
def reconKids (S : Schema) (t : TypeRef) (p : Path) (F : PathSet) (L : List PE) : Option PathSet :=
  L.foldl (fun a x => optU a (reconKid S t p F x)) none

theorem reconKids_snoc (S : Schema) (t : TypeRef) (p : Path) (F : PathSet) (L : List PE) (x : PE) :
    reconKids S t p F (L ++ [x]) = optU (reconKids S t p F L) (reconKid S t p F x) := by
  unfold reconKids; rw [List.foldl_append]; rfl

theorem reconKids_nil (S : Schema) (t : TypeRef) (p : Path) (F : PathSet) :
    reconKids S t p F [] = none := rfl

def kidS (S : Schema) (t : TypeRef) (p : Path) (F : PathSet) (x : PE) : PathSet :=
  match reconChild S t x with
  | some t' => outS S t' (p ++ [x]) (decide (x ∉ F.heads)) (F.under x)
  | none => PathSet.empty

theorem reconKid_toO (S : Schema) (t : TypeRef) (p : Path) (F : PathSet) (x : PE) :
    reconKid S t p F x = toO (kidS S t p F x) := by
  unfold reconKid kidS
  split
  · exact reconOut_toO _ _ _ _ _ (by simp)
  · rfl

theorem foldl_toO (S : Schema) (t : TypeRef) (p : Path) (F : PathSet) :
    ∀ (L : List PE) (A : PathSet),
      L.foldl (fun a x => optU a (reconKid S t p F x)) (toO A) =
        toO (L.foldl (fun a x => PathSet.union a (kidS S t p F x)) A)
  | [], _ => rfl
  | x :: L, A => by
    simp only [List.foldl_cons]
    rw [reconKid_toO, optU_toO]
    exact foldl_toO S t p F L _

theorem mem_foldl_union (S : Schema) (t : TypeRef) (p : Path) (F : PathSet) :
    ∀ (L : List PE) (A : PathSet) (q : Path),
      q ∈ L.foldl (fun a x => PathSet.union a (kidS S t p F x)) A ↔
        q ∈ A ∨ ∃ x, x ∈ L ∧ q ∈ kidS S t p F x
  | [], _, q => by simp
  | x :: L, A, q => by
    simp only [List.foldl_cons]
    rw [mem_foldl_union S t p F L]; unfold PathSet.union; rw [FSet.mem_union']
    constructor
    · rintro ((h | h) | ⟨y, hy, h⟩)
      · exact Or.inl h
      · exact Or.inr ⟨x, List.mem_cons_self .., h⟩
      · exact Or.inr ⟨y, List.mem_cons_of_mem _ hy, h⟩
    · rintro (h | ⟨y, hy, h⟩)
      · exact Or.inl (Or.inl h)
      · rcases List.mem_cons.1 hy with rfl | hy
        · exact Or.inl (Or.inr h)
        · exact Or.inr ⟨y, hy, h⟩

theorem mem_strictPrefixes : ∀ (r n : Path), n ∈ strictPrefixes r ↔ ∃ s, s ≠ [] ∧ r = n ++ s
  | [], n => by
    simp only [strictPrefixes, List.not_mem_nil, false_iff, not_exists, not_and]
    intro s hs h
    have := congrArg List.length h
    simp at this
    exact hs (List.eq_nil_of_length_eq_zero (by omega))
  | e :: r, n => by
    simp only [strictPrefixes, List.mem_cons, List.mem_map]
    rw [show (∃ a, a ∈ strictPrefixes r ∧ e :: a = n) ↔ ∃ a, (∃ s, s ≠ [] ∧ r = a ++ s) ∧ e :: a = n
      from exists_congr (fun a => and_congr_left' (mem_strictPrefixes r a))]
    constructor
    · rintro (rfl | ⟨a, ⟨s, hs, rfl⟩, rfl⟩)
      · exact ⟨e :: r, by simp, rfl⟩
      · exact ⟨s, hs, rfl⟩
    · rintro ⟨s, hs, h⟩
      cases n with
      | nil => exact Or.inl rfl
      | cons e' n =>
        simp only [List.cons_append, List.cons.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact Or.inr ⟨n, ⟨s, hs, rfl⟩, rfl⟩

theorem mem_atomicNodes (S : Schema) (t : TypeRef) (F : PathSet) (n : Path) :
    n ∈ atomicNodes S t F ↔ (∃ s r, s ≠ [] ∧ r ∈ F ∧ r = n ++ s) ∧ n ≠ [] ∧
      ∃ t', reconAt S t n = some t' ∧ isAtomicT S t' = true := by
  unfold atomicNodes
  rw [FSet.mem_filter', FSet.mem_bind']
  constructor
  · rintro ⟨⟨r, hr, hn⟩, hp⟩
    obtain ⟨s, hs, rfl⟩ := (mem_strictPrefixes r n).1 hn
    refine ⟨⟨s, _, hs, hr, rfl⟩, ?_, ?_⟩
    · intro h; subst h; simp at hp
    · revert hp
      cases hra : reconAt S t n with
      | none => simp
      | some t' =>
        intro hp
        refine ⟨t', rfl, ?_⟩
        simp only [Bool.and_eq_true] at hp
        exact hp.2
  · rintro ⟨⟨s, r, hs, hr, rfl⟩, hne, t', hra, hat⟩
    refine ⟨⟨_, hr, (mem_strictPrefixes _ n).2 ⟨s, hs, rfl⟩⟩, ?_⟩
    rw [hra]
    simp only [Bool.and_eq_true, hat, and_true]
    cases n with
    | nil => exact absurd rfl hne
    | cons _ _ => rfl

theorem reconAt_cons (S : Schema) (t : TypeRef) (hg : isGranularT S t = true) (x : PE) (n : Path) :
    reconAt S t (x :: n) = match reconChild S t x with
      | some t' => reconAt S t' n
      | none => none := by
  rw [reconAt]; simp only [hg, ↓reduceIte]
  cases reconChild S t x <;> rfl

theorem isAtomicT_touch (S : Schema) (t : TypeRef) (G : PathSet) (hG : G.isEmpty = false) :
    reconTouch S t false G = isAtomicT S t := by
  unfold reconTouch isAtomicT
  simp only [Bool.not_false, Bool.true_and]
  split <;> simp_all

/-- **`reconBelow` is the children's**: at a granular node, over any `L` covering the set's
children (`heads`). -/
theorem reconKids_eq (S : Schema) (t : TypeRef) (p : Path) (F : PathSet)
    (hg : isGranularT S t = true) (L : List PE) (hL : ∀ x, x ∈ F.heads → x ∈ L) :
    reconKids S t p F L = reconBelow S t p F := by
  unfold reconKids
  rw [show (none : Option PathSet) = toO PathSet.empty from rfl, foldl_toO, reconBelow_toO]
  apply toO_congr
  intro q
  rw [mem_foldl_union, FSet.mem_map']
  simp only [show ∀ q, q ∈ (PathSet.empty : PathSet) ↔ False from fun q => ⟨FSet.mem_empty q, False.elim⟩,
    false_or]
  constructor
  · rintro ⟨x, -, hq⟩
    unfold kidS at hq
    cases hc : reconChild S t x with
    | none => rw [hc] at hq; exact absurd hq (FSet.mem_empty q)
    | some t' =>
      rw [hc] at hq
      unfold outS at hq
      unfold PathSet.union at hq; rw [FSet.mem_union'] at hq
      rcases hq with hq | hq
      · -- the child itself, touched
        split at hq
        · rename_i hT
          have hq' : q = p ++ [x] := by
            have := (PathSet_mem_ofList_law_holds _ _).1 hq
            simpa using this.1
          subst hq'
          have hxh : x ∈ F.heads := by
            by_cases hn : x ∈ F.heads
            · exact hn
            · simp [reconTouch, hn] at hT
          obtain ⟨s, hs, hm⟩ := (PathSet_mem_heads_law_holds _ _).1 hxh
          refine ⟨[x], ?_, rfl⟩
          rw [mem_atomicNodes]
          refine ⟨⟨s, _, hs, hm, rfl⟩, by simp, t', ?_, ?_⟩
          · rw [reconAt_cons S t hg, hc]; rfl
          · have hd : decide (x ∉ F.heads) = false := by simp [hxh]
            rw [hd] at hT
            have hne : (F.under x).isEmpty = false := by
              cases h : (F.under x).isEmpty
              · rfl
              · exact absurd ((PathSet_mem_under_law_holds _ _ _).2 ⟨hs, hm⟩)
                  ((FSet.isEmpty_iff' _).1 h s)
            rw [← isAtomicT_touch S t' _ hne]; exact hT
        · exact absurd hq (FSet.mem_empty q)
      · -- below the child
        obtain ⟨n, hn, rfl⟩ := (FSet.mem_map' _ _ _).1 hq
        rw [mem_atomicNodes] at hn
        obtain ⟨⟨s, r, hs, hr, rfl⟩, hne, t'', hra, hat⟩ := hn
        have hr' := (PathSet_mem_under_law_holds _ _ _).1 hr
        refine ⟨x :: n, ?_, by simp⟩
        rw [mem_atomicNodes]
        refine ⟨⟨s, _, hs, hr'.2, by simp⟩, by simp, t'', ?_, hat⟩
        rw [reconAt_cons S t hg, hc]; exact hra
  · rintro ⟨n, hn, rfl⟩
    rw [mem_atomicNodes] at hn
    obtain ⟨⟨s, r, hs, hr, rfl⟩, hne, t'', hra, hat⟩ := hn
    cases n with
    | nil => exact absurd rfl hne
    | cons x n =>
      have hxh : x ∈ F.heads :=
        (PathSet_mem_heads_law_holds _ _).2 ⟨n ++ s, by simp [hs], by simpa using hr⟩
      refine ⟨x, hL x hxh, ?_⟩
      rw [reconAt_cons S t hg] at hra
      unfold kidS
      cases hc : reconChild S t x with
      | none => rw [hc] at hra; cases hra
      | some t' =>
        rw [hc] at hra
        simp only at hra
        unfold outS PathSet.union
        rw [FSet.mem_union']
        cases n with
        | nil =>
          left
          simp only [reconAt, Option.some.injEq] at hra
          subst hra
          have hd : decide (x ∉ F.heads) = false := by simp [hxh]
          have hne' : (F.under x).isEmpty = false := by
            cases h : (F.under x).isEmpty
            · rfl
            · exact absurd ((PathSet_mem_under_law_holds _ _ _).2 ⟨hs, by simpa using hr⟩)
                ((FSet.isEmpty_iff' _).1 h s)
          rw [hd, isAtomicT_touch S _ _ hne', hat]
          simp only [↓reduceIte]
          exact (PathSet_mem_ofList_law_holds _ _).2 ⟨by simp, by simp⟩
        | cons y n =>
          right
          rw [FSet.mem_map']
          refine ⟨y :: n, ?_, by simp⟩
          rw [mem_atomicNodes]
          refine ⟨⟨s, _, hs, (PathSet_mem_under_law_holds _ _ _).2 ⟨by simp, by simpa using hr⟩, rfl⟩,
            by simp, t'', hra, hat⟩

/-- The final accumulator: the parent's joined with the children's. -/
theorem optU_twice (R X : Option PathSet) : optU R (optU R X) = optU R X := optU_idem_law_holds R X

/-! ## The child's type resolves -/

theorem reconChild_resolves (S : Schema) (hS : S.WF) (t : TypeRef) (a : Atom) (hf : S.find t.name = some a)
    (x : PE) (t' : TypeRef) (hc : reconChild S t x = some t') : (S.find t'.name).isSome := by
  have hw := LawB.find_wf S hS _ _ hf
  unfold reconChild at hc
  rw [hf] at hc
  cases a with
  | scalar _ => cases hc
  | list e rel ks =>
    simp only [Option.some.injEq] at hc; subst hc
    simp only [Atom.wf, Bool.and_eq_true] at hw
    exact hw.1
  | map fs e rel =>
    simp only [Atom.wf, Bool.and_eq_true, List.all_eq_true] at hw
    obtain ⟨⟨-, hfs⟩, he⟩ := hw
    have he' : ∀ t'', e = some t'' → S.resolves t'' = true := by
      intro t'' h; subst h; exact he
    cases x with
    | field n =>
      simp only [fieldType] at hc
      split at hc
      · rename_i t'' hl
        simp only [Option.some.injEq] at hc; subst hc
        exact hfs _ (LawB.lkv_mem hl)
      · exact he' _ hc
    | _ => exact he' _ hc

/-! ## `handleElement`'s child -/

/-- The child set `SetNodeMap.Get` gives (`ok`: found). -/
def childSet (F : PathSet) (x : PE) (ok : Bool) : Option PathSet :=
  if ok then some (F.deep.under x) else none

/-- The child walker's `reconOut` is the child's contribution: reached with `isAtomic =
isMember && !hasChildren`, a child set exactly when it has children. -/
theorem reconKid_eq (S : Schema) (t : TypeRef) (p : Path) (F : PathSet) (x : PE) (e : TypeRef)
    (hc : reconChild S t x = some e) (b ok : Bool) (hok : ok = true ↔ x ∈ F.deep.heads)
    (hb : b = false → x ∈ F.heads) :
    reconOut S e (p ++ [x]) (b && !ok) ((childSet F x ok).getD PathSet.empty) =
      reconKid S t p F x := by
  unfold reconKid childSet
  rw [hc]
  rw [deep_heads] at hok
  cases ok
  · have hx : x ∉ F.heads := fun h => absurd (hok.2 h) (by decide)
    have hb' : b = true := by
      cases b
      · exact absurd (hb rfl) hx
      · rfl
    subst hb'
    simp only [Option.getD, Bool.not_false, Bool.and_true, Bool.false_eq_true, ↓reduceIte]
    rw [under_empty F x hx]
    simp [hx]
  · have hx : x ∈ F.heads := hok.1 rfl
    simp only [Option.getD, Bool.not_true, Bool.and_false, ↓reduceIte]
    rw [deep_under]
    simp [hx]

theorem childSet_atomic (F : PathSet) (x : PE) (b ok : Bool) :
    (b && !ok) = true → childSet F x ok = none := by
  cases ok <;> simp [childSet]

theorem childSet_card (F : PathSet) (x : PE) (ok : Bool) (n : Nat) (hn : 0 < n) (h : F.CardLt n) :
    ((childSet F x ok).getD PathSet.empty).CardLt n := by
  unfold childSet
  cases ok
  · exact hn
  · simp only [↓reduceIte, Option.getD]
    rw [deep_under]
    exact under_cardLt F x n h

/-- The accumulator after one more child. -/
theorem kids_step (S : Schema) (t : TypeRef) (p : Path) (F : PathSet) (L : List PE) (x : PE)
    (R R' X : Option PathSet) (h : optU (optU R (reconKids S t p F L)) R' =
      optU (optU R (reconKids S t p F L)) X) (hX : X = reconKid S t p F x) :
    optU (optU R (reconKids S t p F L)) R' = optU R (reconKids S t p F (L ++ [x])) := by
  rw [h, hX, reconKids_snoc, optU_assoc_law_holds]

/-- The parent's accumulator at the end. -/
theorem kids_final (S : Schema) (t : TypeRef) (p : Path) (F : PathSet) (L : List PE) (R : Option PathSet)
    (hg : isGranularT S t = true) (hL : ∀ x, x ∈ F.heads → x ∈ L) :
    optU R (optU R (reconKids S t p F L)) = optU R (reconBelow S t p F) := by
  rw [optU_idem_law_holds, reconKids_eq S t p F hg L hL]

end LawBR

section st
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **The reconcile walker between `visitListItems`/`visitMapItems`' children**: its errors so far
(none), its struct (path `ps`, child set `fs`, live object `tv` unchanged), path, accumulators
holding `Rc`, `Ac`, spare walkers (the caller's, once there are some). -/
def LawBR.rwVisit (errs_ptr w sc : Loc) (S : Schema) (st : RWSt) (ps : fieldpath.Path) (fs tv sp : Loc)
    (Rc Ac : Option PathSet) : IProp GF :=
  iprop(∃ (sp1 rem1 add1 : Loc) (el : GoSlice), errs_ptr ↦ el ∗ noErrs el ∗
    rwCore w sc S st ps fs tv rem1 add1 sp1 ∗ ownPath ps st.path ∗ isSetO rem1 Rc ∗ isSetO add1 Ac ∗
    spareWalkers _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.typed.reconcileWithSchemaWalker sp1 ∗
    ⌜sp ≠ null → sp1 = sp⌝)

end st

end smd
end EtcdGrove
end Perennial

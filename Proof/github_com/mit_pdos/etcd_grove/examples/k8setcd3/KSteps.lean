/-
Lean-first (no Rocq counterpart).

# The driver's model: its configurations, against `linkv/PendModel.lean`'s (stage 6a)

`Model(st0)` keeps a state as a list of configurations (`mcfg`), each a store and the failed
writes that may still take effect (`pend`). As linkvtxn's `Steps.lean`, here are the pure forms of
`step`, `addConfig`, `Step`'s loops and `closure`'s successors (`stepL`, `addConfigL`, `stepAllL`,
`succAt`) and how they represent the model `pSeq (kSpec st0)`; a configuration is the model's
(`PCfg GSt Input`: the model is stated on the Go records, `KModel.lean`), so no abstraction:

- `CfgEquiv`, `setOf`, `GClosed`, `GOk`, `ClosureOk` as in linkvtxn;
- **`step_closure_ok`**: `Step`'s result, the `closure` of `stepAllL gs x y`, represents
  `ppost S x (ansOf y)` and is closed.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8setcd3.KModel

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8setcd3

open github_com.mit_pdos.etcd_grove.examples.k8setcd3 (Input Output item)
open Classical

section go
variable [GooseExts]

/-- A configuration's contents (`mcfg`): the model's. -/
abbrev GCfg := linkv.PCfg GSt Input

instance GCfg_decEq : DecidableEq GCfg := fun a b =>
  decidable_of_iff (a.st = b.st ∧ a.pend = b.pend) (by cases a; cases b; simp)

/-- `addConfig(s, c)`: `s`, or `s` with `c` appended if no configuration of `s` equals it. -/
def addConfigL (gs : List GCfg) (g : GCfg) : List GCfg := if g ∈ gs then gs else gs ++ [g]

/-- `step(c, in, out)`. -/
def stepL (g : GCfg) (x : Input) (y : Output) : List GCfg :=
  if y.Err' = W64 4 then (if isWriteL x then [⟨g.st, x :: g.pend⟩] else [g])
  else if y = (mstepL x g.st).2 then [⟨(mstepL x g.st).1, g.pend⟩] else []

/-- `Step`'s inner loop, over one configuration's steps. -/
def stepOneL (x : Input) (y : Output) (acc : List GCfg) (g : GCfg) : List GCfg :=
  (stepL g x y).foldl addConfigL acc

/-- `Step`'s loops, before `closure`. -/
def stepAllL (gs : List GCfg) (x : Input) (y : Output) : List GCfg :=
  gs.foldl (stepOneL x y) []

/-- `removeAt(pend, i)`. -/
def removeAtL (es : List Input) (i : Nat) : List Input := es.take i ++ es.drop (i + 1)

/-- The `i`-th pending input of `g` (a default past the end). -/
def pendAt (g : GCfg) (i : Nat) : Input := g.pend.getD i zeroValDef

/-- The configuration `closure` pushes for `g`'s `i`-th pending input: it takes effect. -/
def succAt (g : GCfg) (i : Nat) : GCfg := ⟨(mstepL (pendAt g i) g.st).1, removeAtL g.pend i⟩

/-- The configurations `closure` pushes for `g`'s first `j` pending inputs. -/
def succsUpTo (g : GCfg) (j : Nat) : List GCfg := (List.range j).map (succAt g)

/-! ## The representation -/

variable (st0 : GSt)

/-- The same store, and the same pending inputs up to order. -/
def CfgEquiv (a b : GCfg) : Prop := a.st = b.st ∧ a.pend.Perm b.pend

/-- The set a Go state represents. -/
def setOf (gs : List GCfg) : linkv.PSet GSt Input := fun c => ∃ g ∈ gs, CfgEquiv g c

/-- A Go state is closed under pending writes taking effect. -/
def GClosed (gs : List GCfg) : Prop :=
  ∀ g ∈ gs, ∀ c, linkv.PReach (kSpec st0) g c → ∃ g' ∈ gs, CfgEquiv g' c

/-- The Go state `gs` represents `S`, and is closed. -/
def GOk (gs : List GCfg) (S : linkv.PSet GSt Input) : Prop := GClosed st0 gs ∧ S = setOf gs

/-- What `closure(s)` returns of the configurations `gs` of `s`: configurations reached from
`gs`, and (up to equivalence) every configuration reached from `gs`. -/
def ClosureOk (gs out : List GCfg) : Prop :=
  (∀ g' ∈ out, ∃ g ∈ gs, linkv.PReach (kSpec st0) g g') ∧
  (∀ g ∈ gs, ∀ c, linkv.PReach (kSpec st0) g c → ∃ g' ∈ out, CfgEquiv g' c)

/-! ## The helpers -/

theorem CfgEquiv.refl (c : GCfg) : CfgEquiv c c := ⟨rfl, List.Perm.refl _⟩

theorem CfgEquiv.trans {a b c : GCfg} (h1 : CfgEquiv a b) (h2 : CfgEquiv b c) : CfgEquiv a c :=
  ⟨h1.1.trans h2.1, h1.2.trans h2.2⟩

variable {st0} in
/-- Equivalent configurations reach each other. -/
theorem CfgEquiv.reach {a b : GCfg} (h : CfgEquiv a b) : linkv.PReach (kSpec st0) a b := by
  have hs := linkv.PSilent.perm (P := kSpec st0) a b.pend h.2.symm
  have e : (⟨a.st, b.pend⟩ : GCfg) = b := by rw [h.1]
  rw [e] at hs
  exact linkv.PReach.single hs

theorem perm_getElem_cons_removeAt {α : Type} (l : List α) (i : Nat) (h : i < l.length) :
    l.Perm (l[i] :: (l.take i ++ l.drop (i + 1))) := by
  have e2 : l.drop i = l[i] :: l.drop (i + 1) := List.drop_eq_getElem_cons h
  have e3 : l.take i ++ l[i] :: l.drop (i + 1) = l := by
    rw [← e2]; exact List.take_append_drop i l
  have hm := @List.perm_middle _ l[i] (l.take i) (l.drop (i + 1))
  rw [e3] at hm
  exact hm

theorem pendAt_eq (g : GCfg) (i : Nat) (hi : i < g.pend.length) : pendAt g i = g.pend[i] := by
  unfold pendAt; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; rfl

/-- `removeAt` of the `i`-th, against `erase` of it, up to order. -/
theorem removeAt_perm (g : GCfg) (i : Nat) (hi : i < g.pend.length) (l : List Input)
    (hl : g.pend.Perm l) (hm : pendAt g i ∈ l) :
    (removeAtL g.pend i).Perm (l.erase (pendAt g i)) := by
  have h1 := perm_getElem_cons_removeAt g.pend i hi
  rw [← pendAt_eq g i hi] at h1
  have h2 := List.perm_cons_erase hm
  exact List.Perm.cons_inv (h1.symm.trans (hl.trans h2))

theorem mem_removeAtL {es : List Input} {i : Nat} {p : Input} (h : p ∈ removeAtL es i) :
    p ∈ es := by
  rcases List.mem_append.1 h with h | h
  · exact List.mem_of_mem_take h
  · exact List.mem_of_mem_drop h

theorem length_removeAtL (es : List Input) (i : Nat) (h : i < es.length) :
    (removeAtL es i).length = es.length - 1 := by
  simp only [removeAtL, List.length_append, List.length_take, List.length_drop]
  omega

variable {st0} in
/-- `succAt g i` is reached from `g`: its pending input takes effect. -/
theorem reach_succAt (g : GCfg) (i : Nat) (hi : i < g.pend.length) :
    linkv.PReach (kSpec st0) g (succAt g i) := by
  have hm : pendAt g i ∈ g.pend := by rw [pendAt_eq g i hi]; exact List.getElem_mem hi
  refine .step (.apply _ _ hm) (CfgEquiv.reach ⟨rfl, ?_⟩)
  exact (removeAt_perm g i hi _ (List.Perm.refl _) hm).symm

/-! ## `closure`: a closed list -/

/-- A list whose configurations' successors are in it is closed. -/
theorem closed_of_succ (out : List GCfg)
    (hs : ∀ g ∈ out, ∀ i < g.pend.length, succAt g i ∈ out) : GClosed st0 out := by
  intro g hg c hr
  suffices H : ∀ a b, linkv.PReach (kSpec st0) a b → ∀ g ∈ out, CfgEquiv g a →
      ∃ g' ∈ out, CfgEquiv g' b from H _ _ hr g hg (CfgEquiv.refl _)
  intro a b hr
  induction hr with
  | refl => exact fun g hg he => ⟨g, hg, he⟩
  | @step c₀ c₁ c₂ hs1 _ ih =>
    intro g hg he
    cases hs1 with
    | apply j hm =>
      have hm' : j ∈ g.pend := he.2.mem_iff.2 hm
      obtain ⟨m, hmi, hgi⟩ := List.getElem_of_mem hm'
      have hpi : pendAt g m = j := by rw [pendAt_eq g m hmi, hgi]
      refine ih (succAt g m) (hs g hg m hmi) ⟨?_, ?_⟩
      · show (mstepL (pendAt g m) g.st).1 = _
        rw [hpi, he.1]
      · have := removeAt_perm g m hmi c₀.pend he.2 (by rw [hpi]; exact hm)
        rw [hpi] at this
        exact this
    | perm p hp =>
      exact ih g hg ⟨he.1, he.2.trans hp.symm⟩

theorem succsUpTo_succ (g : GCfg) (j : Nat) :
    succsUpTo g (j + 1) = succsUpTo g j ++ [succAt g j] := by
  simp [succsUpTo, List.range_succ]

theorem mem_succsUpTo (g h : GCfg) (j : Nat) :
    h ∈ succsUpTo g j ↔ ∃ i < j, succAt g i = h := by
  simp [succsUpTo]

/-! ## The bound -/

/-- **A configuration's bound**: its items and pending inputs fewer than `n` (the Go model's
`make`s of `len + 1` never overflow; a step adds at most one to the count, a pending write taking
effect nothing). -/
def Bounded (n : Nat) (g : GCfg) : Prop := g.st.items.length + g.pend.length < n

/-- `setItem`'s loop state's potential: the output's length, one more until `it` is written. -/
def setPot (st : List item × Bool) : Nat := st.1.length + if st.2 then 0 else 1

theorem setPot_step (it : item) (acc : List item × Bool) (e : item) :
    setPot (setStepI it acc e) ≤ setPot acc + 1 := by
  obtain ⟨o, d⟩ := acc
  unfold setStepI setPot
  cases d <;> by_cases h1 : go.GoStringLt it.key' e.key' <;> by_cases h2 : e.key' = it.key' <;>
    simp [h1, h2, go.goStringLt_irrefl]

theorem setPot_foldl (it : item) (l : List item) (acc : List item × Bool) :
    setPot (l.foldl (setStepI it) acc) ≤ setPot acc + l.length := by
  induction l generalizing acc with
  | nil => simp
  | cons e l ih =>
    simp only [List.foldl_cons, List.length_cons]
    have := ih (setStepI it acc e)
    have := setPot_step it acc e
    omega

theorem setItemL_length (its : List item) (it : item) :
    (setItemL its it).length ≤ its.length + 1 := by
  have h := setPot_foldl it its ([], false)
  unfold setItemL
  simp only
  generalize its.foldl (setStepI it) ([], false) = st at h
  obtain ⟨o, d⟩ := st
  cases d <;> simp_all [setPot] <;> omega

theorem delItemL_length (its : List item) (k : GoString) :
    (delItemL its k).length ≤ its.length := List.length_filter_le _ _

theorem mcreateL_length (x : Input) (st : GSt) :
    (mcreateL x st).1.items.length ≤ st.items.length + 1 := by
  unfold mcreateL
  split
  · simp
  · exact setItemL_length _ _

theorem mdeleteL_length (x : Input) (st : GSt) :
    (mdeleteL x st).1.items.length ≤ st.items.length + 1 := by
  unfold mdeleteL
  dsimp only
  split
  · simp
  · split
    · simp
    · have := delItemL_length st.items x.Key'
      simp only; omega

theorem mupdateL_length (x : Input) (st : GSt) :
    (mupdateL x st).1.items.length ≤ st.items.length + 1 := by
  unfold mupdateL
  dsimp only
  split
  · simp
  · split
    · simp
    · split
      · simp
      · exact setItemL_length _ _

/-- A step adds at most one item. -/
theorem mstepL_length (x : Input) (st : GSt) :
    (mstepL x st).1.items.length ≤ st.items.length + 1 := by
  unfold mstepL
  split
  · exact mcreateL_length x st
  · split
    · exact mdeleteL_length x st
    · split
      · exact mupdateL_length x st
      · simp

/-- `succAt g i` keeps the bound. -/
theorem succAt_bounded (n : Nat) (g : GCfg) (i : Nat) (hb : Bounded n g)
    (hi : i < g.pend.length) : Bounded n (succAt g i) := by
  have h1 := mstepL_length (pendAt g i) g.st
  have h2 := length_removeAtL g.pend i hi
  unfold Bounded at hb ⊢
  simp only [succAt]
  omega

/-! ## `closure`: its loop invariant -/

/-- `closure`'s loop invariant, on `out` and `work` (see `closure.lean`). -/
def CloInv (gs : List GCfg) (n : Nat) (out work : List GCfg) : Prop :=
  (∀ g ∈ out ++ work, (∃ g₀ ∈ gs, linkv.PReach (kSpec st0) g₀ g) ∧ Bounded n g) ∧
  (∀ g₀ ∈ gs, g₀ ∈ out ++ work) ∧
  (∀ g ∈ out, ∀ i < g.pend.length, succAt g i ∈ out ++ work)

theorem cloInv_init (gs : List GCfg) (n : Nat) (hb : ∀ g ∈ gs, Bounded n g) :
    CloInv st0 gs n [] gs := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    simp only [List.nil_append] at hg
    exact ⟨⟨g, hg, .refl _⟩, hb g hg⟩
  · intro g hg; simpa using hg
  · intro g hg; cases hg

/-- A configuration already in `out`: dropped. -/
theorem cloInv_skip (gs : List GCfg) (n : Nat) (out work : List GCfg) (h : GCfg)
    (hI : CloInv st0 gs n out (work ++ [h])) (hm : h ∈ out) : CloInv st0 gs n out work := by
  obtain ⟨h1, h2, h3⟩ := hI
  have sub : ∀ g, g ∈ out ++ (work ++ [h]) → g ∈ out ++ work := by
    intro g hg
    simp only [List.mem_append, List.mem_singleton] at hg ⊢
    rcases hg with hg | hg | rfl
    · exact Or.inl hg
    · exact Or.inr hg
    · exact Or.inl hm
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    refine h1 g ?_
    simp only [List.mem_append, List.mem_singleton] at hg ⊢
    rcases hg with hg | hg
    · exact Or.inl hg
    · exact Or.inr (Or.inl hg)
  · intro g₀ hg₀; exact sub _ (h2 g₀ hg₀)
  · intro g hg i hi; exact sub _ (h3 g hg i hi)

/-- A configuration not yet in `out`: added, and its successors pushed. -/
theorem cloInv_add (gs : List GCfg) (n : Nat) (out work : List GCfg)
    (h : GCfg) (hI : CloInv st0 gs n out (work ++ [h])) (hm : h ∉ out) :
    CloInv st0 gs n (out ++ [h]) (work ++ succsUpTo h h.pend.length) := by
  obtain ⟨h1, h2, h3⟩ := hI
  have hh := h1 h (by simp)
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_append, List.mem_singleton] at hg
    rcases hg with (hg | rfl) | hg | hg
    · exact h1 g (by simp [hg])
    · exact hh
    · exact h1 g (by simp [hg])
    · obtain ⟨i, hi, rfl⟩ := (mem_succsUpTo h g _).1 hg
      obtain ⟨⟨g₀, hg₀, hr⟩, hb⟩ := hh
      exact ⟨⟨g₀, hg₀, hr.trans (reach_succAt h i hi)⟩, succAt_bounded n h i hb hi⟩
  · intro g₀ hg₀
    have := h2 g₀ hg₀
    simp only [List.mem_append, List.mem_singleton] at this ⊢
    rcases this with h' | h' | rfl
    · exact Or.inl (Or.inl h')
    · exact Or.inr (Or.inl h')
    · exact Or.inl (Or.inr rfl)
  · intro g hg i hi
    simp only [List.mem_append, List.mem_singleton] at hg ⊢
    rcases hg with hg | rfl
    · have := h3 g hg i hi
      simp only [List.mem_append, List.mem_singleton] at this
      rcases this with h' | h' | rfl
      · exact Or.inl (Or.inl h')
      · exact Or.inr (Or.inl h')
      · exact Or.inl (Or.inr rfl)
    · exact Or.inr (Or.inr ((mem_succsUpTo _ _ _).2 ⟨i, hi, rfl⟩))

/-- At the end of `closure`'s loop (`work` empty): `ClosureOk`, closed, bounded. -/
theorem cloInv_done (gs : List GCfg) (n : Nat) (out : List GCfg) (hI : CloInv st0 gs n out []) :
    ClosureOk st0 gs out ∧ GClosed st0 out ∧ ∀ g ∈ out, Bounded n g := by
  obtain ⟨h1, h2, h3⟩ := hI
  simp only [List.append_nil] at h1 h2 h3
  have hc : GClosed st0 out := closed_of_succ st0 out h3
  exact ⟨⟨fun g hg => (h1 g hg).1, fun g₀ hg₀ c hr => hc g₀ (h2 g₀ hg₀) c hr⟩, hc,
    fun g hg => (h1 g hg).2⟩

/-! ## `step` -/

theorem ansOf_err (y : Output) : ansOf y = .err ↔ y.Err' = W64 4 := by
  unfold ansOf; by_cases h : y.Err' = W64 4 <;> simp [h]

variable {st0} in
/-- A configuration's step by `stepL` is a `PStep`. -/
theorem stepL_sound (g : GCfg) (x : Input) (y : Output) (g' : GCfg) (hg' : g' ∈ stepL g x y) :
    linkv.PStep (kSpec st0) g x (ansOf y) g' := by
  unfold stepL at hg'
  by_cases he : y.Err' = W64 4
  · rw [(ansOf_err y).2 he]
    rw [if_pos he] at hg'
    by_cases hw : isWriteL x = true
    · rw [if_pos hw, List.mem_singleton] at hg'; subst hg'
      exact .errW g x hw
    · rw [if_neg hw, List.mem_singleton] at hg'; subst g'
      exact .errR g x (by simpa using hw)
  · rw [if_neg he] at hg'
    split at hg'
    · next heq =>
      rw [List.mem_singleton] at hg'; subst hg'
      have e1 : ansOf y = .ok ((kSpec st0).step x g.st).2 := by
        unfold ansOf; rw [if_neg he, heq]
      rw [e1]
      exact .ok g x
    · cases hg'

variable {st0} in
/-- A `PStep` of a configuration equivalent to `g` is one of `stepL g`, up to equivalence. -/
theorem stepL_complete (g : GCfg) (x : Input) (y : Output) (c c₁ : GCfg)
    (he : CfgEquiv g c) (hs : linkv.PStep (kSpec st0) c x (ansOf y) c₁) :
    ∃ g' ∈ stepL g x y, CfgEquiv g' c₁ := by
  have hst : c.st = g.st := he.1.symm
  unfold stepL
  generalize hO : ansOf y = o at hs
  cases hs with
  | ok =>
    have hE : ¬ y.Err' = W64 4 := fun h => by rw [(ansOf_err y).2 h] at hO; cases hO
    have hy : y = (mstepL x g.st).2 := by
      unfold ansOf at hO; rw [if_neg hE] at hO
      have := linkv.Ans.ok.inj hO
      rw [this, hst]
    rw [if_neg hE]
    simp only [hy, ↓reduceIte, List.mem_singleton, exists_eq_left]
    refine ⟨?_, he.2⟩
    show (mstepL x g.st).1 = _
    rw [hst]
  | errW hw =>
    have hE : y.Err' = W64 4 := (ansOf_err y).1 hO
    have hw' : isWriteL x = true := hw
    rw [if_pos hE]
    simp only [hw', ↓reduceIte, List.mem_singleton, exists_eq_left]
    exact ⟨he.1, he.2.cons x⟩
  | errR hw =>
    have hE : y.Err' = W64 4 := (ansOf_err y).1 hO
    have hw' : isWriteL x = false := hw
    rw [if_pos hE]
    simp only [hw', Bool.false_eq_true, ↓reduceIte, List.mem_singleton, exists_eq_left]
    exact he

/-! ## `addConfig` and `Step`'s loops -/

theorem mem_addConfigL (gs : List GCfg) (g h : GCfg) :
    h ∈ addConfigL gs g ↔ h ∈ gs ∨ h = g := by
  unfold addConfigL
  split
  · next hg => constructor
               · exact Or.inl
               · rintro (h1 | rfl) <;> assumption
  · simp

theorem length_addConfigL (gs : List GCfg) (g : GCfg) :
    (addConfigL gs g).length = if g ∈ gs then gs.length else gs.length + 1 := by
  unfold addConfigL; split <;> simp

theorem mem_foldl_addConfigL (l acc : List GCfg) (h : GCfg) :
    h ∈ l.foldl addConfigL acc ↔ h ∈ acc ∨ h ∈ l := by
  induction l generalizing acc with
  | nil => simp
  | cons g l ih =>
    simp only [List.foldl_cons, ih, mem_addConfigL, List.mem_cons]
    exact or_assoc

theorem mem_stepAllL (gs : List GCfg) (x : Input) (y : Output) (h : GCfg) :
    h ∈ stepAllL gs x y ↔ ∃ g ∈ gs, h ∈ stepL g x y := by
  unfold stepAllL
  suffices H : ∀ acc, h ∈ gs.foldl (stepOneL x y) acc ↔ h ∈ acc ∨ ∃ g ∈ gs, h ∈ stepL g x y by
    simpa using H []
  induction gs with
  | nil => simp
  | cons g gs ih =>
    intro acc
    simp only [List.foldl_cons, ih, stepOneL, mem_foldl_addConfigL, List.mem_cons]
    constructor
    · rintro ((h1 | h1) | ⟨g', hg', h2⟩)
      · exact Or.inl h1
      · exact Or.inr ⟨g, Or.inl rfl, h1⟩
      · exact Or.inr ⟨g', Or.inr hg', h2⟩
    · rintro (h1 | ⟨g', (rfl | hg'), h2⟩)
      · exact Or.inl (Or.inl h1)
      · exact Or.inl (Or.inr h2)
      · exact Or.inr ⟨g', hg', h2⟩

/-- A step keeps the bound, one more. -/
theorem stepL_bounded (n : Nat) (g : GCfg) (x : Input) (y : Output) (hb : Bounded n g)
    (g' : GCfg) (hg' : g' ∈ stepL g x y) : Bounded (n + 1) g' := by
  unfold Bounded at hb ⊢
  unfold stepL at hg'
  split at hg'
  · split at hg'
    · simp only [List.mem_singleton] at hg'; subst hg'
      simp only [List.length_cons]; omega
    · simp only [List.mem_singleton] at hg'; subst hg'; omega
  · split at hg'
    · simp only [List.mem_singleton] at hg'; subst hg'
      have := mstepL_length x g.st
      simp only; omega
    · cases hg'

/-- `Step`'s loops keep the bound, one more. -/
theorem stepAllL_bounded (n : Nat) (gs : List GCfg) (x : Input) (y : Output)
    (hb : ∀ g ∈ gs, Bounded n g) : ∀ g' ∈ stepAllL gs x y, Bounded (n + 1) g' := by
  intro g' hg'
  obtain ⟨g, hg, hs⟩ := (mem_stepAllL gs x y g').1 hg'
  exact stepL_bounded n g x y (hb g hg) g' hs

/-! ## `Step` -/

/-- **`Step`'s result** (see the file header): the `closure` `out` of `stepAllL gs x y`
represents `ppost S x (ansOf y)` and is closed. -/
theorem step_closure_ok (gs out : List GCfg) (S : linkv.PSet GSt Input) (x : Input) (y : Output)
    (hS : GOk st0 gs S) (hc : ClosureOk st0 (stepAllL gs x y) out) (hcl : GClosed st0 out) :
    GOk st0 out (linkv.ppost (kSpec st0) S x (ansOf y)) := by
  refine ⟨hcl, ?_⟩
  obtain ⟨hgs, rfl⟩ := hS
  funext c'
  apply propext
  constructor
  · rintro ⟨c₀, c, c₁, ⟨g₀, hg₀, he₀⟩, hr₀, hs, hr₁⟩
    obtain ⟨g, hg, he⟩ := hgs g₀ hg₀ c (he₀.reach.trans hr₀)
    obtain ⟨g₁, hg₁, he₁⟩ := stepL_complete g x y c c₁ he hs
    have hm : g₁ ∈ stepAllL gs x y := (mem_stepAllL gs x y g₁).2 ⟨g, hg, hg₁⟩
    exact hc.2 g₁ hm c' (he₁.reach.trans hr₁)
  · rintro ⟨g', hg', he'⟩
    obtain ⟨g₁, hg₁, hr⟩ := hc.1 g' hg'
    obtain ⟨g, hg, hs⟩ := (mem_stepAllL gs x y g₁).1 hg₁
    have hcs := stepL_sound (st0 := st0) g x y g₁ hs
    exact ⟨g, g, g₁, ⟨g, hg, CfgEquiv.refl _⟩, .refl _, hcs, hr.trans he'.reach⟩

/-- A representation is empty only when its list is. -/
theorem setOf_nonempty (gs : List GCfg) : (∃ c, setOf gs c) ↔ gs ≠ [] := by
  constructor
  · rintro ⟨c, g, hg, -⟩ h; subst h; cases hg
  · intro h
    cases gs with
    | nil => exact absurd rfl h
    | cons g _ => exact ⟨g, g, List.mem_cons_self, CfgEquiv.refl _⟩

/-- `Init()`'s configuration: the seeded store, nothing pending. -/
def gInit : GCfg := ⟨st0, []⟩

theorem bounded_gInit : Bounded (st0.items.length + 1) (gInit st0) := by
  unfold Bounded gInit; simp

/-- The initial state: one configuration. -/
theorem gok_init : GOk st0 [gInit st0] (linkv.pInit (kSpec st0)) := by
  have hset : linkv.pInit (kSpec st0) = setOf [gInit st0] := by
    funext c
    apply propext
    simp only [linkv.pInit, setOf, List.mem_singleton, exists_eq_left, gInit, CfgEquiv]
    constructor
    · rintro rfl; exact ⟨rfl, List.Perm.refl _⟩
    · rintro ⟨h1, h2⟩
      have : c = ⟨c.st, c.pend⟩ := rfl
      rw [this, ← h1, ← List.Perm.eq_nil h2.symm]
  refine ⟨?_, hset⟩
  intro g hg c hr
  simp only [List.mem_singleton] at hg
  subst hg
  have hc : linkv.pInit (kSpec st0) c := linkv.pInit_closed _ _ rfl hr
  refine ⟨gInit st0, List.mem_singleton_self _, ?_⟩
  rw [hc]; exact CfgEquiv.refl _

end go

end k8setcd3
end EtcdGrove
end Perennial

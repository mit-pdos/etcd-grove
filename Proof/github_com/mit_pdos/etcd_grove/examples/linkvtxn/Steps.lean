/-
Lean-first (no Rocq counterpart).

# linkvtxn: the Go model's configurations, against `linkvtxn/PendModel.lean`'s (linkv-txn stage E)

`examples/linkvtxn/linkvtxn.go`'s `Model()` keeps a state as a list of configurations (`mcfg`),
each a store and the failed writes that may still take effect (`pend`, a list of `Input`s). As
`linkv/ModelLemmas.lean` does for `examples/linkv`, here are the pure forms of `step`,
`addConfig`, `Step`'s loops and `closure`'s successors (`GCfg`, `stepL`, `addConfigL`,
`stepAllL`, `succAt`), and how they abstract to the model `pSeq (txnSpec wks)`:

- `absCfg g`: the model configuration (`absSt` of the store; the pending inputs decoded, `decP`);
  `CfgEquiv`, `setOf`, `GClosed`, `GOk`, `ClosureOk` as in `linkv`;
- `Bounded n g`: the invariant a configuration keeps: a good store (`GoodSt`), every pending
  input one `Gen` may return (`ValidIn`), and the revision plus the pending count at most `n`
  (`mstep`'s revision never overflows: a step adds at most one to the sum, a pending write taking
  effect nothing; a state of porcupine's index `k` has `n = k + 1`);
- **`step_closure_ok`**: for an input `Gen` may return, `Step`'s result, the `closure` of
  `stepAllL gs x y`, represents `ppost S (decP x) (decOut x.Kind' y)` and is closed (the model's
  operation is the input decoded and the output decoded by the input's kind: `Abs.lean`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.linkvtxn.Abs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace linkvtxn

open github_com.mit_pdos.etcd_grove.examples.linkvtxn
open Classical

section go
variable [GooseExts]

/-- The model's inputs, outputs and states. -/
abbrev MI := linkv.MIn GoString GoString
abbrev MO := linkv.MOut GoString GoString
abbrev MS := linkv.MSt GoString GoString

/-- The model: `TxnModel.lean`'s, listing the workload's keys. -/
abbrev TS : linkv.PendSpec MS MI MO := linkv.txnSpec wks

/-- A model configuration. -/
abbrev MC := linkv.PCfg MS MI

/-! ## The Go helpers' pure functions -/

/-- A configuration's contents (`mcfg`). -/
structure GCfg where
  st : GSt
  pend : List Input

instance GCfg_decEq : DecidableEq GCfg := fun a b =>
  decidable_of_iff (a.st = b.st ∧ a.pend = b.pend) (by cases a; cases b; simp)

/-- `addConfig(s, c)`: `s`, or `s` with `c` appended if no configuration of `s` equals it. -/
def addConfigL (gs : List GCfg) (g : GCfg) : List GCfg := if g ∈ gs then gs else gs ++ [g]

/-- `step(c, in, out)`. -/
def stepL (g : GCfg) (x : Input) (y : Output) : List GCfg :=
  if y.Err' then (if isWriteL x then [⟨g.st, x :: g.pend⟩] else [g])
  else if outEqualL x.Kind' y (mstepL x g.st).2 then [⟨(mstepL x g.st).1, g.pend⟩] else []

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

/-! ## The abstraction -/

/-- A pending input's model input (a default for one that does not decode, which a pending input
never is: `Bounded`). -/
def decP (x : Input) : MI := (decIn x).getD .list

/-- A configuration's model configuration. -/
def absCfg (g : GCfg) : MC := ⟨absSt g.st, g.pend.map decP⟩

/-- The same store, and the same pending inputs up to order. -/
def CfgEquiv (a b : MC) : Prop := a.st = b.st ∧ a.pend.Perm b.pend

/-- The set a Go state represents. -/
def setOf (gs : List GCfg) : linkv.PSet MS MI := fun c => ∃ g ∈ gs, CfgEquiv (absCfg g) c

/-- A Go state is closed under pending writes taking effect. -/
def GClosed (gs : List GCfg) : Prop :=
  ∀ g ∈ gs, ∀ c, linkv.PReach TS (absCfg g) c → ∃ g' ∈ gs, CfgEquiv (absCfg g') c

/-- The Go state `gs` represents `S`, and is closed. -/
def GOk (gs : List GCfg) (S : linkv.PSet MS MI) : Prop := GClosed gs ∧ S = setOf gs

/-- What `closure(s)` returns of the configurations `gs` of `s`: configurations reached from
`gs`, and (up to equivalence) every configuration reached from `gs`. -/
def ClosureOk (gs out : List GCfg) : Prop :=
  (∀ g' ∈ out, ∃ g ∈ gs, linkv.PReach TS (absCfg g) (absCfg g')) ∧
  (∀ g ∈ gs, ∀ c, linkv.PReach TS (absCfg g) c → ∃ g' ∈ out, CfgEquiv (absCfg g') c)

/-- The invariant of a configuration (see the file header). -/
def Bounded (n : Nat) (g : GCfg) : Prop :=
  GoodSt g.st ∧ (∀ p ∈ g.pend, ValidIn p) ∧ uint.nat g.st.rev + g.pend.length ≤ n

/-! ## The helpers -/

theorem uintZ_succ_lt (r : w64) (h : uint.nat r < 2 ^ 63) : uint.Z r + 1 < 2 ^ 64 := by
  unfold uint.nat at h; word

theorem decP_of (x : Input) (i : MI) (h : decIn x = some i) : decP x = i := by
  simp [decP, h]

/-- **An input's step on a good store**: the model's (store and output), the store stays good, and
the revision moves by at most one. -/
theorem mstep_ok (x : Input) (hx : ValidIn x) (st : GSt) (hg : GoodSt st)
    (hr : uint.nat st.rev < 2 ^ 63) :
    absSt (mstepL x st).1 = (linkv.mStep wks (decP x) (absSt st)).1 ∧
      decOut x.Kind' (mstepL x st).2 = .ok (linkv.mStep wks (decP x) (absSt st)).2 ∧
      GoodSt (mstepL x st).1 ∧ uint.nat (mstepL x st).1.rev ≤ uint.nat st.rev + 1 := by
  obtain ⟨i, hi, hk⟩ := hx
  rw [decP_of x i hi]
  have hr' : uint.Z st.rev + 1 < 2 ^ 64 := uintZ_succ_lt _ hr
  obtain ⟨h1, h2, h3⟩ := mstepL_abs x i hi hk st hg hr'
  refine ⟨h1, h2, h3, ?_⟩
  have := (linkv.mStep_rev_le wks i (absSt st)).2
  have e : uint.nat (mstepL x st).1.rev = (absSt (mstepL x st).1).rev := rfl
  rw [e, h1]; exact this

theorem decOut_err (k : w64) (y : Output) : decOut k y = .err ↔ y.Err' = true := by
  unfold decOut; cases y.Err' <;> simp

theorem CfgEquiv.refl (c : MC) : CfgEquiv c c := ⟨rfl, List.Perm.refl _⟩

theorem CfgEquiv.trans {a b c : MC} (h1 : CfgEquiv a b) (h2 : CfgEquiv b c) : CfgEquiv a c :=
  ⟨h1.1.trans h2.1, h1.2.trans h2.2⟩

/-- Equivalent configurations reach each other. -/
theorem CfgEquiv.reach {a b : MC} (h : CfgEquiv a b) : linkv.PReach TS a b := by
  have hs := linkv.PSilent.perm (P := TS) a b.pend h.2.symm
  rw [h.1] at hs
  exact linkv.PReach.single hs

theorem perm_getElem_cons_removeAt {α : Type} (l : List α) (i : Nat) (h : i < l.length) :
    l.Perm (l[i] :: (l.take i ++ l.drop (i + 1))) := by
  have e2 : l.drop i = l[i] :: l.drop (i + 1) := List.drop_eq_getElem_cons h
  have e3 : l.take i ++ l[i] :: l.drop (i + 1) = l := by
    rw [← e2]; exact List.take_append_drop i l
  have hm := @List.perm_middle _ l[i] (l.take i) (l.drop (i + 1))
  rw [e3] at hm
  exact hm

/-- `List.perm_cons_erase` at the model's instance of `BEq`. -/
theorem pend_perm_cons_erase {α : Type} [DecidableEq α] {l : List α} {a : α} (h : a ∈ l) :
    l.Perm (a :: l.erase a) := List.perm_cons_erase h

theorem pendAt_eq (g : GCfg) (i : Nat) (hi : i < g.pend.length) : pendAt g i = g.pend[i] := by
  unfold pendAt; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; rfl

/-- `removeAt` of the `i`-th, against `erase` of its decoded input, up to order. -/
theorem removeAt_perm (g : GCfg) (i : Nat) (hi : i < g.pend.length) (l : List MI)
    (hl : (g.pend.map decP).Perm l) (hm : decP (pendAt g i) ∈ l) :
    ((removeAtL g.pend i).map decP).Perm (l.erase (decP (pendAt g i))) := by
  have hlen : (g.pend.map decP).length = g.pend.length := List.length_map _
  have h1 := perm_getElem_cons_removeAt (g.pend.map decP) i (by rw [hlen]; exact hi)
  rw [List.getElem_map, ← pendAt_eq g i hi] at h1
  have h2 := pend_perm_cons_erase hm
  simp only [removeAtL, List.map_append, List.map_take, List.map_drop]
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

/-- `succAt g i`'s store: the `i`-th pending input's step. -/
theorem succAt_st (n : Nat) (g : GCfg) (i : Nat) (hb : Bounded n g) (hn : n < 2 ^ 63)
    (hi : i < g.pend.length) :
    absSt (succAt g i).st = (linkv.mStep wks (decP (pendAt g i)) (absSt g.st)).1 ∧
      Bounded n (succAt g i) := by
  have hv : ValidIn (pendAt g i) := by
    rw [pendAt_eq g i hi]; exact hb.2.1 _ (List.getElem_mem hi)
  have hb3 := hb.2.2
  obtain ⟨h1, -, h3, h4⟩ := mstep_ok _ hv g.st hb.1 (by omega)
  refine ⟨h1, h3, fun p hp => hb.2.1 p (mem_removeAtL hp), ?_⟩
  have := length_removeAtL g.pend i hi
  simp only [succAt]
  omega

/-- `succAt g i` is reached from `g`: its pending input takes effect. -/
theorem reach_succAt (n : Nat) (g : GCfg) (i : Nat) (hb : Bounded n g) (hn : n < 2 ^ 63)
    (hi : i < g.pend.length) : linkv.PReach TS (absCfg g) (absCfg (succAt g i)) := by
  have hm : decP (pendAt g i) ∈ (absCfg g).pend := by
    unfold absCfg; rw [pendAt_eq g i hi]; exact List.mem_map_of_mem (List.getElem_mem hi)
  refine .step (.apply _ _ hm) (CfgEquiv.reach ⟨?_, ?_⟩)
  · exact (succAt_st n g i hb hn hi).1.symm
  · exact (removeAt_perm g i hi _ (List.Perm.refl _) hm).symm

/-! ## `closure`: a closed list -/

/-- A list whose configurations' successors are in it is closed. -/
theorem closed_of_succ (n : Nat) (hn : n < 2 ^ 63) (out : List GCfg)
    (hb : ∀ g ∈ out, Bounded n g)
    (hs : ∀ g ∈ out, ∀ i < g.pend.length, succAt g i ∈ out) : GClosed out := by
  intro g hg c hr
  suffices H : ∀ a b, linkv.PReach TS a b → ∀ g ∈ out, CfgEquiv (absCfg g) a →
      ∃ g' ∈ out, CfgEquiv (absCfg g') b from H _ _ hr g hg (CfgEquiv.refl _)
  intro a b hr
  induction hr with
  | refl => exact fun g hg he => ⟨g, hg, he⟩
  | @step c₀ c₁ c₂ hs1 _ ih =>
    intro g hg he
    cases hs1 with
    | apply j hm =>
      -- the pending input `j` is `g`'s `m`-th
      have hm' : j ∈ g.pend.map decP := he.2.mem_iff.2 hm
      obtain ⟨m, hmi, hgi⟩ := List.getElem_of_mem hm'
      rw [List.length_map] at hmi
      have hpi : decP (pendAt g m) = j := by
        rw [pendAt_eq g m hmi, ← hgi, List.getElem_map]
      obtain ⟨h1, -⟩ := succAt_st n g m (hb g hg) hn hmi
      refine ih (succAt g m) (hs g hg m hmi) ⟨?_, ?_⟩
      · show absSt (succAt g m).st = _
        rw [h1, hpi, show absSt g.st = c₀.st from he.1]; rfl
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

/-- `closure`'s loop invariant, on `out` and `work` (see `closure.lean`). -/
def CloInv (gs : List GCfg) (n : Nat) (out work : List GCfg) : Prop :=
  (∀ g ∈ out ++ work, (∃ g₀ ∈ gs, linkv.PReach TS (absCfg g₀) (absCfg g)) ∧ Bounded n g) ∧
  (∀ g₀ ∈ gs, g₀ ∈ out ++ work) ∧
  (∀ g ∈ out, ∀ i < g.pend.length, succAt g i ∈ out ++ work)

theorem cloInv_init (gs : List GCfg) (n : Nat) (hb : ∀ g ∈ gs, Bounded n g) :
    CloInv gs n [] gs := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    simp only [List.nil_append] at hg
    exact ⟨⟨g, hg, .refl _⟩, hb g hg⟩
  · intro g hg; simpa using hg
  · intro g hg; cases hg

/-- A configuration already in `out`: dropped. -/
theorem cloInv_skip (gs : List GCfg) (n : Nat) (out work : List GCfg) (h : GCfg)
    (hI : CloInv gs n out (work ++ [h])) (hm : h ∈ out) : CloInv gs n out work := by
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
theorem cloInv_add (gs : List GCfg) (n : Nat) (hn : n < 2 ^ 63) (out work : List GCfg)
    (h : GCfg) (hI : CloInv gs n out (work ++ [h])) (hm : h ∉ out) :
    CloInv gs n (out ++ [h]) (work ++ succsUpTo h h.pend.length) := by
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
      exact ⟨⟨g₀, hg₀, hr.trans (reach_succAt n h i hb hn hi)⟩, (succAt_st n h i hb hn hi).2⟩
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
theorem cloInv_done (gs : List GCfg) (n : Nat) (hn : n < 2 ^ 63) (out : List GCfg)
    (hI : CloInv gs n out []) :
    ClosureOk gs out ∧ GClosed out ∧ ∀ g ∈ out, Bounded n g := by
  obtain ⟨h1, h2, h3⟩ := hI
  simp only [List.append_nil] at h1 h2 h3
  have hc : GClosed out := closed_of_succ n hn out (fun g hg => (h1 g hg).2) h3
  exact ⟨⟨fun g hg => (h1 g hg).1, fun g₀ hg₀ c hr => hc g₀ (h2 g₀ hg₀) c hr⟩, hc,
    fun g hg => (h1 g hg).2⟩

/-! ## `step` -/

/-- A step keeps the invariant, the bound one more. -/
theorem stepL_bounded (n : Nat) (hn : n < 2 ^ 63) (g : GCfg) (x : Input) (hx : ValidIn x)
    (y : Output) (hb : Bounded n g) (g' : GCfg) (hg' : g' ∈ stepL g x y) :
    Bounded (n + 1) g' := by
  have hb3 := hb.2.2
  unfold stepL at hg'
  split at hg'
  · split at hg'
    · simp only [List.mem_singleton] at hg'; subst hg'
      refine ⟨hb.1, ?_, ?_⟩
      · intro p hp
        rcases List.mem_cons.1 hp with rfl | hp
        · exact hx
        · exact hb.2.1 p hp
      · simp only [List.length_cons]; omega
    · simp only [List.mem_singleton] at hg'; subst hg'
      exact ⟨hb.1, hb.2.1, by omega⟩
  · split at hg'
    · simp only [List.mem_singleton] at hg'; subst hg'
      obtain ⟨-, -, h3, h4⟩ := mstep_ok x hx g.st hb.1 (by omega)
      exact ⟨h3, hb.2.1, by simp only; omega⟩
    · cases hg'

/-- A configuration's step by `stepL` is a `PStep` of its model configuration. -/
theorem stepL_sound (n : Nat) (hn : n < 2 ^ 63) (g : GCfg) (hb : Bounded n g) (x : Input)
    (hx : ValidIn x) (y : Output) (g' : GCfg) (hg' : g' ∈ stepL g x y) :
    linkv.PStep TS (absCfg g) (decP x) (decOut x.Kind' y) (absCfg g') := by
  obtain ⟨i, hi, hk⟩ := hx
  have hdi := decP_of x i hi
  unfold stepL at hg'
  by_cases he : y.Err' = true
  · rw [(decOut_err x.Kind' y).2 he]
    rw [if_pos he] at hg'
    by_cases hw : isWriteL x = true
    · rw [if_pos hw, List.mem_singleton] at hg'; subst hg'
      have hw' : TS.isWrite (decP x) = true := by
        rw [hdi]; show i.isWrite = true; rw [← isWriteL_dec x i hi]; exact hw
      exact .errW (absCfg g) (decP x) hw'
    · rw [if_neg hw, List.mem_singleton] at hg'; subst g'
      have hw' : TS.isWrite (decP x) = false := by
        rw [hdi]; show i.isWrite = false; rw [← isWriteL_dec x i hi]; simpa using hw
      exact .errR (absCfg g) (decP x) hw'
  · rw [if_neg he] at hg'
    split at hg'
    · next heq =>
      rw [List.mem_singleton] at hg'; subst hg'
      have hb3 := hb.2.2
      obtain ⟨h1, -, -, -⟩ := mstep_ok x ⟨i, hi, hk⟩ g.st hb.1 (by omega)
      have hr' : uint.Z g.st.rev + 1 < 2 ^ 64 := uintZ_succ_lt _ (by omega)
      have e1 : decOut x.Kind' y = .ok (TS.step (decP x) (absCfg g).st).2 := by
        rw [hdi]; exact (outEqualL_mstep x i hi hk g.st hb.1 hr' y).1 heq
      have e2 : absCfg ⟨(mstepL x g.st).1, g.pend⟩ =
          ⟨(TS.step (decP x) (absCfg g).st).1, (absCfg g).pend⟩ := by
        show (⟨absSt (mstepL x g.st).1, g.pend.map decP⟩ : MC) = _
        rw [h1]; rfl
      rw [e1, e2]
      exact .ok _ _
    · cases hg'

/-- A `PStep` of a configuration equivalent to `g`'s is one of `stepL g`, up to equivalence. -/
theorem stepL_complete (n : Nat) (hn : n < 2 ^ 63) (g : GCfg) (hb : Bounded n g) (x : Input)
    (hx : ValidIn x) (y : Output) (c c₁ : MC) (he : CfgEquiv (absCfg g) c)
    (hs : linkv.PStep TS c (decP x) (decOut x.Kind' y) c₁) :
    ∃ g' ∈ stepL g x y, CfgEquiv (absCfg g') c₁ := by
  obtain ⟨i, hi, hk⟩ := hx
  have hdi := decP_of x i hi
  have hst : c.st = absSt g.st := he.1.symm
  unfold stepL
  generalize hI : decP x = j at hs
  generalize hO : decOut x.Kind' y = o at hs
  cases hs with
  | ok =>
    have hE : y.Err' = false := by
      cases h : y.Err'
      · rfl
      · rw [(decOut_err x.Kind' y).2 h] at hO; cases hO
    have hb3 := hb.2.2
    have hr' : uint.Z g.st.rev + 1 < 2 ^ 64 := uintZ_succ_lt _ (by omega)
    obtain ⟨h1, -, -, -⟩ := mstep_ok x ⟨i, hi, hk⟩ g.st hb.1 (by omega)
    have heq : outEqualL x.Kind' y (mstepL x g.st).2 = true := by
      refine (outEqualL_mstep x i hi hk g.st hb.1 hr' y).2 ?_
      rw [hO, ← hdi, hI, hst]; rfl
    rw [hE]
    simp only [Bool.false_eq_true, ↓reduceIte, heq, List.mem_singleton, exists_eq_left]
    refine ⟨?_, he.2⟩
    show absSt (mstepL x g.st).1 = _
    rw [h1, hI, hst]; rfl
  | errW hw =>
    have hE : y.Err' = true := (decOut_err x.Kind' y).1 hO
    have hw' : isWriteL x = true := by
      rw [isWriteL_dec x i hi, ← hdi, hI]; exact hw
    rw [hE]
    simp only [↓reduceIte, hw', List.mem_singleton, exists_eq_left]
    refine ⟨he.1, ?_⟩
    show (decP x :: g.pend.map decP).Perm _
    rw [hI]; exact he.2.cons j
  | errR hw =>
    have hE : y.Err' = true := (decOut_err x.Kind' y).1 hO
    have hw' : isWriteL x = false := by
      rw [isWriteL_dec x i hi, ← hdi, hI]; exact hw
    rw [hE]
    simp only [↓reduceIte, hw', Bool.false_eq_true, List.mem_singleton, exists_eq_left]
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

/-- `Step`'s loops keep the invariant, the bound one more. -/
theorem stepAllL_bounded (n : Nat) (hn : n < 2 ^ 63) (gs : List GCfg) (x : Input)
    (hx : ValidIn x) (y : Output) (hb : ∀ g ∈ gs, Bounded n g) :
    ∀ g' ∈ stepAllL gs x y, Bounded (n + 1) g' := by
  intro g' hg'
  obtain ⟨g, hg, hs⟩ := (mem_stepAllL gs x y g').1 hg'
  exact stepL_bounded n hn g x hx y (hb g hg) g' hs

/-! ## `Step` -/

/-- **`Step`'s result** (see the file header): the `closure` `out` of `stepAllL gs x y`
represents `ppost S (decP x) (decOut x.Kind' y)` and is closed. -/
theorem step_closure_ok (n : Nat) (hn : n < 2 ^ 63) (gs out : List GCfg) (S : linkv.PSet MS MI)
    (x : Input) (hx : ValidIn x) (y : Output) (hb : ∀ g ∈ gs, Bounded n g) (hS : GOk gs S)
    (hc : ClosureOk (stepAllL gs x y) out) (hcl : GClosed out) :
    GOk out (linkv.ppost TS S (decP x) (decOut x.Kind' y)) := by
  refine ⟨hcl, ?_⟩
  obtain ⟨hgs, rfl⟩ := hS
  funext c'
  apply propext
  constructor
  · -- a configuration of `ppost`: from `g₀ ∈ gs`, pending writes, the step, pending writes
    rintro ⟨c₀, c, c₁, ⟨g₀, hg₀, he₀⟩, hr₀, hs, hr₁⟩
    obtain ⟨g, hg, he⟩ := hgs g₀ hg₀ c (he₀.reach.trans hr₀)
    obtain ⟨g₁, hg₁, he₁⟩ := stepL_complete n hn g (hb g hg) x hx y c c₁ he hs
    have hm : g₁ ∈ stepAllL gs x y := (mem_stepAllL gs x y g₁).2 ⟨g, hg, hg₁⟩
    exact hc.2 g₁ hm c' (he₁.reach.trans hr₁)
  · -- a configuration of `out`: reached from a step of a configuration of `gs`
    rintro ⟨g', hg', he'⟩
    obtain ⟨g₁, hg₁, hr⟩ := hc.1 g' hg'
    obtain ⟨g, hg, hs⟩ := (mem_stepAllL gs x y g₁).1 hg₁
    have hcs := stepL_sound n hn g (hb g hg) x hx y g₁ hs
    exact ⟨absCfg g, absCfg g, absCfg g₁, ⟨g, hg, CfgEquiv.refl _⟩, .refl _, hcs,
      hr.trans he'.reach⟩

/-- A representation is empty only when its list is. -/
theorem setOf_nonempty (gs : List GCfg) : (∃ c, setOf gs c) ↔ gs ≠ [] := by
  constructor
  · rintro ⟨c, g, hg, -⟩ h; subst h; cases hg
  · intro h
    cases gs with
    | nil => exact absurd rfl h
    | cons g _ => exact ⟨absCfg g, g, List.mem_cons_self, CfgEquiv.refl _⟩

/-- `Init()`'s configuration: the empty store at revision `1`, nothing pending. -/
def gInit : GCfg := ⟨⟨[], W64 1⟩, []⟩

theorem absCfg_gInit : absCfg gInit = ⟨TS.init, []⟩ := by
  have h1 : uint.nat (W64 1) = 1 := by unfold uint.nat; word
  show (⟨⟨absStore [], uint.nat (W64 1)⟩, []⟩ : MC) = ⟨⟨fun _ => none, 1⟩, []⟩
  rw [h1]; rfl

theorem bounded_gInit : Bounded 1 gInit := by
  have h1 : uint.nat (W64 1) = 1 := by unfold uint.nat; word
  refine ⟨⟨List.Pairwise.nil, fun e he => (by cases he)⟩, ⟨fun p hp => (by cases hp), ?_⟩⟩
  show uint.nat (W64 1) + 0 ≤ 1
  omega

/-- The initial state: one configuration. -/
theorem gok_init : GOk [gInit] (linkv.pInit TS) := by
  have hset : linkv.pInit TS = setOf [gInit] := by
    funext c
    apply propext
    simp only [linkv.pInit, setOf, List.mem_singleton, exists_eq_left, absCfg_gInit, CfgEquiv]
    constructor
    · rintro rfl; exact ⟨rfl, List.Perm.refl _⟩
    · rintro ⟨h1, h2⟩
      have : c = ⟨c.st, c.pend⟩ := rfl
      rw [this, ← h1, ← List.Perm.eq_nil h2.symm]
  refine ⟨?_, hset⟩
  intro g hg c hr
  simp only [List.mem_singleton] at hg
  subst hg
  have hc : linkv.pInit TS c := linkv.pInit_closed _ _ absCfg_gInit hr
  refine ⟨gInit, List.mem_singleton_self _, ?_⟩
  rw [absCfg_gInit, hc]; exact CfgEquiv.refl _

end go

end linkvtxn
end EtcdGrove
end Perennial

/-
The tester's history (`history`, `examples/mvccfull/mvccfull.go`): its ghost state and lock.
Lean-first (no Rocq counterpart); mvccrand's (`History.lean` there), with the compactions.

The writer appends each revision it makes (`appendRev`, under the write lock of `h.mu`): the
revision's state (a map, never changed once appended) and its changes (a slice, likewise); and each
successful compaction's revision (`addComp`, under the same lock). Readers take a snapshot of the
states (`snapshot`), one revision's changes (`changesAt`) or look a compaction up (`compPrev`) under
the read lock. So:

- **The revisions** are a monotone ghost list `γ.l` of `HRev`s (state, changes), the `r`-th the
  revision `r`'s. Its authoritative element is split between the lock (half, fractionally) and the
  writer (half, `histW`): only the writer appends, and it knows the list exactly. A lower bound
  (`monoListLbOwn γ.l Hs`, persistent) is what every other thread holds of it.
- **What the lock guards** (`histR h γ q`, fractional): the fields `states`, `changes` and `comps`
  (the slices), a ghost variable `γ.g` of the cells' contents (`HistCells`; half, fractionally; the
  writer has the other half), the list's authoritative half, and persistently the slices' elements,
  each map's and each change slice's points-to (`histElems`). The slices' capacities are the
  writer's (`histW`): only it appends. The compactions `cps` are in the cells only (the writer knows
  them exactly through its half of `γ.g`; a reader under the lock sees them).
- **A thread's handle** (`histRd h γ`, exclusive): the persistent `isHistory` (the lock's guard;
  mvccfull's history has no `published` or `aboveFloor`, mvccrand's had) with one of the lock's
  reader slots.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccfull.Pending
public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccrand.MvccCountable
public import Perennial.Proof.sync.RWMutexGuard
public import Perennial.Ghost.MonoList
public import Perennial.Ghost.GhostVar

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccfull

open Iris Iris.BI Iris.ProofMode github_com.mit_pdos.etcd_grove.examples.mvccfull mvcc mvcc.api

section model
variable [GooseExts]

instance kvRec.countable : Pos.Countable kvRec :=
  .ofInjective (fun e => Pos.Countable.encode (e.val', e.create', e.mod', e.ver', e.lease'))
    (fun a b h => by
      have h := Pos.encode_inj h
      cases a; cases b
      simp only [Prod.mk.injEq] at h
      obtain ⟨h1, h2, h3, h4, h5⟩ := h
      subst h1 h2 h3 h4 h5; rfl)

instance change.countable : Pos.Countable change :=
  .ofInjective (fun c => Pos.Countable.encode (c.del', c.key', c.kv'))
    (fun a b h => by
      have h := Pos.encode_inj h
      cases a; cases b
      simp only [Prod.mk.injEq] at h
      obtain ⟨h1, h2, h3⟩ := h
      subst h1 h2 h3; rfl)

/-- A revision of the history: its state and its changes. -/
abbrev HRev := GMap GoString kvRec × List change

/-- The history's start: revisions `0` and `1`, both empty. -/
def hist0 : List HRev := [(∅, []), (∅, [])]

/-- The history's ghost names. -/
structure HistNames where
  /-- the cells' contents (the lock's half, the writer's half) -/
  g : GName
  /-- the revisions (a monotone list) -/
  l : GName

/-- The history's cells: the three slices, the states' maps and the changes' slices (their
elements), the compactions, and the revisions. -/
structure HistCells where
  states : GoSlice
  changes : GoSlice
  comps : GoSlice
  ms : List GoMap
  cs : List GoSlice
  cps : List w64
  revs : List HRev

instance HistCells.countable : Pos.Countable HistCells :=
  .ofInjective (fun x => Pos.Countable.encode (x.states, x.changes, x.comps, x.ms, x.cs, x.cps, x.revs))
    (fun a b h => by
      have h := Pos.encode_inj h
      cases a; cases b
      simp only [Prod.mk.injEq] at h
      obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
      subst h1 h2 h3 h4 h5 h6 h7; rfl)

end model

section addrs
variable [GooseExts] [GoGlobalContext] [GoSemanticsFunctions]

abbrev hMu (h : Loc) : Loc := structFieldRef history go!"mu" h
abbrev hStates (h : Loc) : Loc := structFieldRef history go!"states" h
abbrev hChanges (h : Loc) : Loc := structFieldRef history go!"changes" h
abbrev hComps (h : Loc) : Loc := structFieldRef history go!"comps" h

end addrs

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccfull.Assumptions]

/-- The states' maps `ms` hold the revisions' states `Hs` (persistent). -/
def statesP (ms : List GoMap) (Hs : List HRev) : IProp GF :=
  iprop(⌜ms.length = Hs.length⌝ ∗ [∗list] x ∈ ms.zip Hs, x.1 ↦$□ x.2.1)

instance statesP_persistent (ms : List GoMap) (Hs : List HRev) :
    Persistent (statesP (GF := GF) ms Hs) := by
  unfold statesP; infer_instance

/-- The changes' slices `cs` hold the revisions' changes `Hs` (persistent). -/
def changesP (cs : List GoSlice) (Hs : List HRev) : IProp GF :=
  iprop(⌜cs.length = Hs.length⌝ ∗ [∗list] x ∈ cs.zip Hs, x.1 ↦*□ x.2.2)

instance changesP_persistent (cs : List GoSlice) (Hs : List HRev) :
    Persistent (changesP (GF := GF) cs Hs) := by
  unfold changesP; infer_instance

/-- The cells' contents, persistently: the three slices' elements and the states' and changes'. -/
def histElems (x : HistCells) : IProp GF :=
  iprop(⌜2 ≤ x.revs.length⌝ ∗ x.states ↦*□ x.ms ∗ x.changes ↦*□ x.cs ∗ x.comps ↦*□ x.cps ∗
    statesP x.ms x.revs ∗ changesP x.cs x.revs)

instance histElems_persistent (x : HistCells) : Persistent (histElems (GF := GF) x) := by
  unfold histElems; infer_instance

/-- **What `h.mu` guards, at `q`** (see the file header). -/
def histR (h : Loc) (γ : HistNames) (q : Qp) : IProp GF :=
  iprop(∃ x : HistCells, hStates h ↦{DFrac.own q} x.states ∗ hChanges h ↦{DFrac.own q} x.changes ∗
    hComps h ↦{DFrac.own q} x.comps ∗
    ghostVar γ.g q.half x ∗ monoListAuthOwn γ.l q.half x.revs ∗ histElems x)

instance histR_timeless (h : Loc) (γ : HistNames) (q : Qp) : Timeless (histR (GF := GF) h γ q) := by
  unfold histR histElems statesP changesP; infer_instance

theorem slice_field_fractional (l : Loc) (q1 q2 : Qp) (v : GoSlice) :
    (l ↦{DFrac.own (q1 + q2)} v : IProp GF) ⊣⊢ l ↦{DFrac.own q1} v ∗ l ↦{DFrac.own q2} v :=
  (typedPointsto_dfractional (GF := GF) l v).dfractional (DFrac.own q1) (DFrac.own q2)

instance histR_fractional (h : Loc) (γ : HistNames) : Fractional (histR (GF := GF) h γ) where
  fractional q1 q2 := by
    have hs := fun v => slice_field_fractional (GF := GF) (hStates h) q1 q2 v
    have hc := fun v => slice_field_fractional (GF := GF) (hChanges h) q1 q2 v
    have hp := fun v => slice_field_fractional (GF := GF) (hComps h) q1 q2 v
    have hg := fun (x : HistCells) => (ghostVar_half_fractional (GF := GF) γ.g x).fractional q1 q2
    have hl : ∀ l : List HRev, (monoListAuthOwn γ.l (q1 + q2).half l : IProp GF) ⊣⊢
        monoListAuthOwn γ.l q1.half l ∗ monoListAuthOwn γ.l q2.half l := fun l => by
      rw [Qp_half_add]; exact (monoListAuthOwn_fractional (GF := GF) γ.l l).fractional q1.half q2.half
    unfold histR
    refine ⟨?_, ?_⟩
    · iintro ⟨%x, Hs, Hc, Hp, Hg, Hl, #He⟩
      icases (hs x.states).1 $$ Hs with ⟨Hs1, Hs2⟩
      icases (hc x.changes).1 $$ Hc with ⟨Hc1, Hc2⟩
      icases (hp x.comps).1 $$ Hp with ⟨Hp1, Hp2⟩
      icases (hg x).1 $$ Hg with ⟨Hg1, Hg2⟩
      icases (hl x.revs).1 $$ Hl with ⟨Hl1, Hl2⟩
      isplitl [Hs1 Hc1 Hp1 Hg1 Hl1]
      · iexists x; iframe; iframe #
      · iexists x; iframe; iframe #
    · iintro ⟨⟨%x1, Hs1, Hc1, Hp1, Hg1, Hl1, #He1⟩, ⟨%x2, Hs2, Hc2, Hp2, Hg2, Hl2, #He2⟩⟩
      ihave %Hag := ghostVar_agree γ.g _ _ _ _ $$ Hg1 Hg2
      subst Hag
      iexists x1
      isplitl [Hs1 Hs2]
      · iapply (hs x1.states).2; iframe
      isplitl [Hc1 Hc2]
      · iapply (hc x1.changes).2; iframe
      isplitl [Hp1 Hp2]
      · iapply (hp x1.comps).2; iframe
      isplitl [Hg1 Hg2]
      · iapply (hg x1).2; iframe
      isplitl [Hl1 Hl2]
      · iapply (hl x1.revs).2; iframe
      iframe #

/-- **`h` is a history named `γ`** (persistent): its lock's guard. -/
def isHistory (h : Loc) (γ : HistNames) : IProp GF :=
  iprop(sync.isRWMutexGuard (hMu h) (histR h γ))

instance isHistory_persistent (h : Loc) (γ : HistNames) : Persistent (isHistory (GF := GF) h γ) := by
  unfold isHistory; infer_instance

/-- **A thread's handle of the history** (exclusive): one of the lock's reader slots. -/
def histRd (h : Loc) (γ : HistNames) : IProp GF :=
  iprop(isHistory h γ ∗ sync.ownRWMutex (hMu h) (histR h γ))

/-- **The writer's part of the history at the revisions `Hs` and the compactions `Cs`**
(exclusive): the other halves, and the slices' capacities. -/
def histW (γ : HistNames) (Hs : List HRev) (Cs : List w64) : IProp GF :=
  iprop(∃ x : HistCells, ⌜x.revs = Hs ∧ x.cps = Cs⌝ ∗ ghostVar γ.g (1 : Qp).half x ∗
    monoListAuthOwn γ.l (1 : Qp).half Hs ∗ ownSliceCap GoMap x.states (DFrac.own 1) ∗
    ownSliceCap GoSlice x.changes (DFrac.own 1) ∗ ownSliceCap w64 x.comps (DFrac.own 1))

/-- The writer's part gives a lower bound of the revisions. -/
theorem histW_lb (γ : HistNames) (Hs : List HRev) (Cs : List w64) :
    histW (GF := GF) γ Hs Cs ⊢ histW γ Hs Cs ∗ monoListLbOwn γ.l Hs := by
  iintro H
  iunfold histW at H
  icases H with ⟨%x, %Hx, Hg, Hl, Hc1, Hc2, Hc3⟩
  ihave #Hlb := monoListLbOwn_get γ.l _ Hs $$ Hl
  iframe #
  iunfold histW
  iexists x
  iframe
  ipureintro; exact Hx

/-- Two slice values with the same pointer and length own the same non-empty elements (a
three-index slice `s[0:n:n]`'s capacity differs from `s`'s). -/
theorem ownSlice_same_ptr_len' {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V]
    (s1 s2 : GoSlice) (dq : DFrac) (vs : List V) :
    vs ≠ [] → s1.ptr = s2.ptr → s1.len = s2.len → sint.Z s2.len ≤ sint.Z s2.cap →
    ⊢ (s1 ↦*{dq} vs : IProp GF) -∗ s2 ↦*{dq} vs := by
  intro Hne Hptr Hlen Hcap
  obtain ⟨p1, l1, c1⟩ := s1
  obtain ⟨p2, l2, c2⟩ := s2
  simp only at Hptr Hlen Hcap
  subst Hptr Hlen
  rw [ownSlice_unseal]; unfold ownSliceDef
  iintro (%H | ⟨H, %_⟩)
  · exact absurd H.2 Hne
  · iright
    iframe H
    ipureintro; exact Hcap

end defs

end mvccfull
end EtcdGrove
end Perennial

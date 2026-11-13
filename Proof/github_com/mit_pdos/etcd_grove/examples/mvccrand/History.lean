/-
The tester's history (`history`, `examples/mvccrand/mvccrand.go`): its ghost state and lock.
Lean-first (no Rocq counterpart).

The writer appends each revision it makes (`appendRev`, under the write lock of `h.mu`): the
revision's state (a map, never changed once appended) and its changes (a slice, likewise). Readers
take a snapshot of the states (`snapshot`) or one revision's changes (`changesAt`) under the read
lock. So:

- **The revisions** are a monotone ghost list `γ.l` of `HRev`s (state, changes), the `r`-th the
  revision `r`'s. Its authoritative element is split between the lock (half, fractionally) and the
  writer (half, `histW`): only the writer appends, and it knows the list exactly. A lower bound
  (`monoListLbOwn γ.l Hs`, persistent) is what every other thread holds of it.
- **What the lock guards** (`histR h γ q`, fractional): the fields `states` and `changes` (the
  slices), a ghost variable `γ.g` of the slices' contents (half, fractionally; the writer has the
  other half), the list's authoritative half, and persistently the slices' elements, each map's and
  each change slice's points-to (`histElems`). The slices' capacities are the writer's (`histW`):
  only it appends.
- **A thread's handle** (`histRd h γ`, exclusive): the persistent `isHistory` (the lock's guard
  and the invariant of `aboveFloor`, a counter nobody checks) with one of the lock's reader slots.
  Not a thread pool: the readers call `snapshot` inside an mvcc transaction, which held their
  thread token when this was designed (no longer: mvcc's contracts take no `threadTok` since
  2026-11-07), so a reader's slot is its own (dealt by `Run`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccrand.Pending
public import Perennial.Proof.sync.RWMutexGuard
public import Perennial.Proof.sync.atomic.Base
public import Perennial.Ghost.MonoList
public import Perennial.Ghost.GhostVar

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccrand

open Iris Iris.BI Iris.ProofMode github_com.mit_pdos.etcd_grove.examples.mvccrand

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

/-- The history's start: revisions `0` and `1`, both empty (`newHistory`). -/
def hist0 : List HRev := [(∅, []), (∅, [])]

/-- The history's ghost names. -/
structure HistNames where
  /-- the slices' contents (the lock's half, the writer's half) -/
  g : GName
  /-- the revisions (a monotone list) -/
  l : GName

/-- The slices' contents: `states`, `changes`, their elements, and the revisions. -/
abbrev HistCells := GoSlice × GoSlice × List GoMap × List GoSlice × List HRev

end model

section addrs
variable [GooseExts] [GoGlobalContext] [GoSemanticsFunctions]

abbrev hMu (h : Loc) : Loc := structFieldRef history go!"mu" h
abbrev hStates (h : Loc) : Loc := structFieldRef history go!"states" h
abbrev hChanges (h : Loc) : Loc := structFieldRef history go!"changes" h
abbrev hPub (h : Loc) : Loc := structFieldRef history go!"published" h
abbrev hAbove (h : Loc) : Loc := structFieldRef history go!"aboveFloor" h

end addrs

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccrand.Assumptions]

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

/-- The cells' contents, persistently: the two slices' elements and theirs. -/
def histElems (x : HistCells) : IProp GF :=
  iprop(⌜2 ≤ x.2.2.2.2.length⌝ ∗ x.1 ↦*□ x.2.2.1 ∗ x.2.1 ↦*□ x.2.2.2.1 ∗
    statesP x.2.2.1 x.2.2.2.2 ∗ changesP x.2.2.2.1 x.2.2.2.2)

instance histElems_persistent (x : HistCells) : Persistent (histElems (GF := GF) x) := by
  unfold histElems; infer_instance

/-- **What `h.mu` guards, at `q`** (see the file header). -/
def histR (h : Loc) (γ : HistNames) (q : Qp) : IProp GF :=
  iprop(∃ x : HistCells, hStates h ↦{DFrac.own q} x.1 ∗ hChanges h ↦{DFrac.own q} x.2.1 ∗
    ghostVar γ.g q.half x ∗ monoListAuthOwn γ.l q.half x.2.2.2.2 ∗ histElems x)

instance histR_timeless (h : Loc) (γ : HistNames) (q : Qp) : Timeless (histR (GF := GF) h γ q) := by
  unfold histR histElems statesP changesP; infer_instance

instance histR_fractional (h : Loc) (γ : HistNames) : Fractional (histR (GF := GF) h γ) where
  fractional q1 q2 := by
    have hs : ∀ v : GoSlice, (hStates h ↦{DFrac.own (q1 + q2)} v : IProp GF) ⊣⊢
        hStates h ↦{DFrac.own q1} v ∗ hStates h ↦{DFrac.own q2} v := fun v =>
      (typedPointsto_dfractional (GF := GF) (hStates h) v).dfractional (DFrac.own q1) (DFrac.own q2)
    have hc : ∀ v : GoSlice, (hChanges h ↦{DFrac.own (q1 + q2)} v : IProp GF) ⊣⊢
        hChanges h ↦{DFrac.own q1} v ∗ hChanges h ↦{DFrac.own q2} v := fun v =>
      (typedPointsto_dfractional (GF := GF) (hChanges h) v).dfractional (DFrac.own q1) (DFrac.own q2)
    have hg := fun (x : HistCells) => (ghostVar_half_fractional (GF := GF) γ.g x).fractional q1 q2
    have hl : ∀ l : List HRev, (monoListAuthOwn γ.l (q1 + q2).half l : IProp GF) ⊣⊢
        monoListAuthOwn γ.l q1.half l ∗ monoListAuthOwn γ.l q2.half l := fun l => by
      rw [Qp_half_add]; exact (monoListAuthOwn_fractional (GF := GF) γ.l l).fractional q1.half q2.half
    unfold histR
    refine ⟨?_, ?_⟩
    · iintro ⟨%x, Hs, Hc, Hg, Hl, #He⟩
      icases (hs x.1).1 $$ Hs with ⟨Hs1, Hs2⟩
      icases (hc x.2.1).1 $$ Hc with ⟨Hc1, Hc2⟩
      icases (hg x).1 $$ Hg with ⟨Hg1, Hg2⟩
      icases (hl x.2.2.2.2).1 $$ Hl with ⟨Hl1, Hl2⟩
      isplitl [Hs1 Hc1 Hg1 Hl1]
      · iexists x; iframe; iframe #
      · iexists x; iframe; iframe #
    · iintro ⟨⟨%x1, Hs1, Hc1, Hg1, Hl1, #He1⟩, ⟨%x2, Hs2, Hc2, Hg2, Hl2, #He2⟩⟩
      ihave %Hag := ghostVar_agree γ.g _ _ _ _ $$ Hg1 Hg2
      subst Hag
      iexists x1
      isplitl [Hs1 Hs2]
      · iapply (hs x1.1).2; iframe
      isplitl [Hc1 Hc2]
      · iapply (hc x1.2.1).2; iframe
      isplitl [Hg1 Hg2]
      · iapply (hg x1).2; iframe
      isplitl [Hl1 Hl2]
      · iapply (hl x1.2.2.2.2).2; iframe
      iframe #

/-- The invariant of `aboveFloor` (any value: the tester reports it, checks nothing of it). -/
def aboveInv (h : Loc) : IProp GF := iprop(∃ a : w64, sync.atomic.ownInt64 (hAbove h) (DFrac.own 1) a)

/-- The history's namespace. -/
def histN : Namespace := (nroot .@ "mvccrand") .@ "hist"

/-- **`h` is a history named `γ`** (persistent): its lock's guard, the counter's invariant. -/
def isHistory (h : Loc) (γ : HistNames) : IProp GF :=
  iprop(sync.isRWMutexGuard (hMu h) (histR h γ) ∗ inv histN (aboveInv h))

instance isHistory_persistent (h : Loc) (γ : HistNames) : Persistent (isHistory (GF := GF) h γ) := by
  unfold isHistory; infer_instance

/-- **A thread's handle of the history** (exclusive): one of the lock's reader slots. -/
def histRd (h : Loc) (γ : HistNames) : IProp GF :=
  iprop(isHistory h γ ∗ sync.ownRWMutex (hMu h) (histR h γ))

/-- **The writer's part of the history at the revisions `Hs`** (exclusive): the other halves, and
the slices' capacities. -/
def histW (γ : HistNames) (Hs : List HRev) : IProp GF :=
  iprop(∃ x : HistCells, ⌜x.2.2.2.2 = Hs⌝ ∗ ghostVar γ.g (1 : Qp).half x ∗
    monoListAuthOwn γ.l (1 : Qp).half Hs ∗ ownSliceCap GoMap x.1 (DFrac.own 1) ∗
    ownSliceCap GoSlice x.2.1 (DFrac.own 1))

/-- The writer's part gives a lower bound of the revisions. -/
theorem histW_lb (γ : HistNames) (Hs : List HRev) :
    histW (GF := GF) γ Hs ⊢ histW γ Hs ∗ monoListLbOwn γ.l Hs := by
  iintro H
  iunfold histW at H
  icases H with ⟨%x, %Hx, Hg, Hl, Hc1, Hc2⟩
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

end mvccrand
end EtcdGrove
end Perennial

/-
Lean-first (no Rocq counterpart).

# linkv: the Go model's pure form, against `KVModel.lean`'s (2026-10-19)

`examples/linkv/linkv.go`'s `Model()` computes on Go values: a state is a list of
configurations (`kvConfig`), each a store (`kv`, a list of `kvEntry`s) and the pending puts
(`pend`, a list of `kvEntry`s). Here are the pure functions the Go helpers compute, as the specs
state them (`Spec/.../linkv/<fn>.lean`), and how they abstract to `KVModel.lean`'s model
(`kvSeq`, `kvM`):

- `GCfg`: a configuration's contents (the two lists); `absCfg g` its `Cfg` (`absStore`: a key's
  value is its first entry's, as `lookup` finds it; the pending puts as pairs);
- the helpers: `lookupL` (`lookup`), `setL` (`set`: the store with `k ↦ v`, `setL_eq`),
  `insertSortedL` (`insertSorted`: a permutation of `e :: pend`), `removeAtL` (`removeAt`),
  `entryLessB`, `addConfigL` (`addConfig`), `stepL` (`step`, the model's `CStep`) and
  `stepAllL` (`Step`'s loops, before `closure`); `succAt g i` is the configuration `closure`
  pushes for `g`'s `i`-th pending put;
- `CfgEquiv a b`: the same store and the same pending puts up to order. A Go state `gs`
  represents the set `setOf gs` (the configurations equivalent to one of `gs`), and is
  *closed* (`GClosed`: every configuration a pending put reaches from one of `gs` is
  equivalent to one of `gs`), `GOk gs S`;
- the decoder `decIO` of an operation's Go input and output (`Input`, `Output`) to the model's
  (`KVIn`, `KVOut`): a put that returned an error, a put that returned no error with no value
  (`ok`), a get's error or its value; any other output (a put with a value, a get not found with
  a value) is no operation of the model, and `step` rejects it (`stepL_none`);
- **`step_closure_ok`**: `Step`'s result, the `closure` of `stepAllL gs x y`, represents
  `post S i o` (`decIO x y = some (i, o)`) and is closed; it is empty when `decIO` rejects.

No invariant on the Go lists is needed: `absStore` reads a key's first entry, which `setL`
replaces (or inserts before), so the store's sortedness (which `set` keeps) is not used, nor are
the pending puts' order (`Silent.perm`) or the state's lack of duplicates (`addConfig`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.linkv.KVModel
public import Code.github_com.mit_pdos.etcd_grove.examples.linkv

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace linkv

open github_com.mit_pdos.etcd_grove.examples.linkv
open Classical

section go
variable [ext : FfiSyntax]

/-! ## The Go helpers' pure functions -/

instance kvEntry_decEq : DecidableEq kvEntry := fun a b =>
  decidable_of_iff (a.key' = b.key' ∧ a.val' = b.val') (by cases a; cases b; simp)

/-- `entryLess(a, b)`. -/
def entryLessB (a b : kvEntry) : Bool :=
  decide (go.GoStringLt a.key' b.key') ||
    (decide (a.key' = b.key') && decide (go.GoStringLt a.val' b.val'))

/-- `lookup(kv, k)`: the value of `k`'s first entry. -/
def lookupL (es : List kvEntry) (k : GoString) : GoString × Bool :=
  match es.find? (fun e => decide (e.key' = k)) with
  | some e => (e.val', true)
  | none => (go!"", false)

/-- One iteration of `set`'s loop on `(out, done)`. -/
def setStep (k v : GoString) (st : List kvEntry × Bool) (e : kvEntry) : List kvEntry × Bool :=
  if st.2 = false ∧ go.GoStringLe k e.key' then
    if e.key' = k then (st.1 ++ [⟨k, v⟩], true) else (st.1 ++ [⟨k, v⟩, e], true)
  else (st.1 ++ [e], st.2)

/-- The end of `set`: `k ↦ v` appended if not yet written. -/
def setFin (k v : GoString) (st : List kvEntry × Bool) : List kvEntry :=
  if st.2 then st.1 else st.1 ++ [⟨k, v⟩]

/-- `set(kv, k, v)`. -/
def setL (es : List kvEntry) (k v : GoString) : List kvEntry :=
  setFin k v (es.foldl (setStep k v) ([], false))

/-- One iteration of `insertSorted`'s loop on `(out, done)`. -/
def insStep (e : kvEntry) (st : List kvEntry × Bool) (x : kvEntry) : List kvEntry × Bool :=
  if st.2 = false ∧ entryLessB x e = false then (st.1 ++ [e, x], true) else (st.1 ++ [x], st.2)

/-- The end of `insertSorted`: `e` appended if not yet inserted. -/
def insFin (e : kvEntry) (st : List kvEntry × Bool) : List kvEntry :=
  if st.2 then st.1 else st.1 ++ [e]

/-- `insertSorted(pend, e)`. -/
def insertSortedL (es : List kvEntry) (e : kvEntry) : List kvEntry :=
  insFin e (es.foldl (insStep e) ([], false))

/-- `removeAt(pend, i)`. -/
def removeAtL (es : List kvEntry) (i : Nat) : List kvEntry := es.take i ++ es.drop (i + 1)

/-- A configuration's contents. -/
structure GCfg where
  kv : List kvEntry
  pend : List kvEntry

instance GCfg_decEq : DecidableEq GCfg := fun a b =>
  decidable_of_iff (a.kv = b.kv ∧ a.pend = b.pend) (by cases a; cases b; simp)

/-- `addConfig(s, c)`: `s`, or `s` with `c` appended if no configuration of `s` equals it. -/
def addConfigL (gs : List GCfg) (g : GCfg) : List GCfg := if g ∈ gs then gs else gs ++ [g]

/-- `step(c, in, out)` (see the file header). -/
def stepL (g : GCfg) (x : Input) (y : Output) : List GCfg :=
  if x.Put' then
    if y.Err' then [⟨g.kv, insertSortedL g.pend ⟨x.Key', x.Val'⟩⟩]
    else if y.Found' ∨ y.Val' ≠ go!"" then []
    else [⟨setL g.kv x.Key' x.Val', g.pend⟩]
  else if y.Err' then [g]
  else
    let r := lookupL g.kv x.Key'
    if r.2 ≠ y.Found' ∨ (r.2 = true ∧ r.1 ≠ y.Val') ∨ (r.2 = false ∧ y.Val' ≠ go!"") then []
    else [g]

/-- `Step`'s inner loop, over one configuration's steps. -/
def stepOneL (x : Input) (y : Output) (acc : List GCfg) (g : GCfg) : List GCfg :=
  (stepL g x y).foldl addConfigL acc

/-- `Step`'s loops, before `closure`. -/
def stepAllL (gs : List GCfg) (x : Input) (y : Output) : List GCfg :=
  gs.foldl (stepOneL x y) []

/-- The `i`-th pending put of `g` (a default past the end). -/
def pendAt (g : GCfg) (i : Nat) : kvEntry := g.pend.getD i ⟨go!"", go!""⟩

/-- The configuration `closure` pushes for `g`'s `i`-th pending put: it takes effect. -/
def succAt (g : GCfg) (i : Nat) : GCfg :=
  ⟨setL g.kv (pendAt g i).key' (pendAt g i).val', removeAtL g.pend i⟩

/-- The configurations `closure` pushes for `g`'s first `j` pending puts. -/
def succsUpTo (g : GCfg) (j : Nat) : List GCfg := (List.range j).map (succAt g)

/-! ## The abstraction -/

/-- A store's value at `k`: its first entry's. -/
def absStore (es : List kvEntry) : Store GoString GoString :=
  fun k => (es.find? (fun e => decide (e.key' = k))).map kvEntry.val'

/-- An entry as a pair. -/
def toPair (e : kvEntry) : GoString × GoString := (e.key', e.val')

/-- A configuration's model configuration. -/
def absCfg (g : GCfg) : Cfg GoString GoString := ⟨absStore g.kv, g.pend.map toPair⟩

/-- The same store, and the same pending puts up to order. -/
def CfgEquiv (a b : Cfg GoString GoString) : Prop := a.kv = b.kv ∧ a.pend.Perm b.pend

/-- The set a Go state represents. -/
def setOf (gs : List GCfg) : KVSet GoString GoString := fun c => ∃ g ∈ gs, CfgEquiv (absCfg g) c

/-- A Go state is closed under pending puts taking effect. -/
def GClosed (gs : List GCfg) : Prop :=
  ∀ g ∈ gs, ∀ c, Reach (absCfg g) c → ∃ g' ∈ gs, CfgEquiv (absCfg g') c

/-- The Go state `gs` represents `S`, and is closed. -/
def GOk (gs : List GCfg) (S : KVSet GoString GoString) : Prop := GClosed gs ∧ S = setOf gs

/-- What `closure(s)` returns of the configurations `gs` of `s`: configurations reached from
`gs`, and (up to equivalence) every configuration reached from `gs`. -/
def ClosureOk (gs out : List GCfg) : Prop :=
  (∀ g' ∈ out, ∃ g ∈ gs, Reach (absCfg g) (absCfg g')) ∧
  (∀ g ∈ gs, ∀ c, Reach (absCfg g) c → ∃ g' ∈ out, CfgEquiv (absCfg g') c)

/-- The decoder of an operation's Go input and output (see the file header). -/
def decIO (x : Input) (y : Output) : Option (KVIn GoString GoString × KVOut GoString) :=
  if x.Put' then
    if y.Err' then some (.put x.Key' x.Val', .err)
    else if y.Found' = false ∧ y.Val' = go!"" then some (.put x.Key' x.Val', .ok) else none
  else if y.Err' then some (.get x.Key', .err)
  else if y.Found' then some (.get x.Key', .okGet (some y.Val'))
  else if y.Val' = go!"" then some (.get x.Key', .okGet none) else none

/-! ## The helpers -/

theorem Cfg.eta' (c : Cfg GoString GoString) : (⟨c.kv, c.pend⟩ : Cfg GoString GoString) = c := rfl

theorem CfgEquiv.refl (c : Cfg GoString GoString) : CfgEquiv c c := ⟨rfl, List.Perm.refl _⟩

theorem CfgEquiv.trans {a b c : Cfg GoString GoString} (h1 : CfgEquiv a b) (h2 : CfgEquiv b c) :
    CfgEquiv a c := ⟨h1.1.trans h2.1, h1.2.trans h2.2⟩

theorem CfgEquiv.symm {a b : Cfg GoString GoString} (h : CfgEquiv a b) : CfgEquiv b a :=
  ⟨h.1.symm, h.2.symm⟩

/-- Equivalent configurations reach each other. -/
theorem CfgEquiv.reach {a b : Cfg GoString GoString} (h : CfgEquiv a b) : Reach a b := by
  have hs := Silent.perm a b.pend h.2.symm
  rw [h.1] at hs
  exact Reach.single hs

theorem absStore_cons (e : kvEntry) (es : List kvEntry) (k : GoString) :
    absStore (e :: es) k = if e.key' = k then some e.val' else absStore es k := by
  unfold absStore
  by_cases h : e.key' = k <;> simp [List.find?_cons, h]

theorem absStore_nil : absStore ([] : List kvEntry) = fun _ => none := rfl

/-- `set`, recursively. -/
def setR (k v : GoString) : List kvEntry → List kvEntry
  | [] => [⟨k, v⟩]
  | e :: es =>
    if go.GoStringLe k e.key' then (if e.key' = k then ⟨k, v⟩ :: es else ⟨k, v⟩ :: e :: es)
    else e :: setR k v es

theorem setStep_done_foldl (k v : GoString) (es out : List kvEntry) :
    es.foldl (setStep k v) (out, true) = (out ++ es, true) := by
  induction es generalizing out with
  | nil => simp
  | cons e es ih =>
    simp only [List.foldl_cons, setStep, Bool.true_eq_false, false_and, if_false]
    rw [ih]; simp

theorem setL_foldl (k v : GoString) (es out : List kvEntry) :
    setFin k v (es.foldl (setStep k v) (out, false)) = out ++ setR k v es := by
  induction es generalizing out with
  | nil => simp [setR, setFin]
  | cons e es ih =>
    simp only [List.foldl_cons]
    by_cases hle : go.GoStringLe k e.key'
    · by_cases he : e.key' = k
      · have hs : setStep k v (out, false) e = (out ++ [⟨k, v⟩], true) := by
          rw [setStep, if_pos (⟨rfl, hle⟩ : (out, false).2 = false ∧ go.GoStringLe k e.key'),
            if_pos he]
        rw [hs, setStep_done_foldl, setR, if_pos hle, if_pos he]; simp [setFin]
      · have hs : setStep k v (out, false) e = (out ++ [⟨k, v⟩, e], true) := by
          rw [setStep, if_pos (⟨rfl, hle⟩ : (out, false).2 = false ∧ go.GoStringLe k e.key'),
            if_neg he]
        rw [hs, setStep_done_foldl, setR, if_pos hle, if_neg he]; simp [setFin]
    · have hs : setStep k v (out, false) e = (out ++ [e], false) := by
        rw [setStep, if_neg (fun h => hle h.2)]
      rw [hs, ih, setR, if_neg hle]; simp

theorem setL_eq (es : List kvEntry) (k v : GoString) : setL es k v = setR k v es := by
  have := setL_foldl k v es []
  simpa [setL] using this

theorem absStore_setR (k v : GoString) (es : List kvEntry) :
    absStore (setR k v es) = (absStore es).set k v := by
  induction es with
  | nil =>
    funext k'
    simp only [setR, absStore_cons, absStore_nil, Store.set]
    by_cases h : k' = k
    · subst h; simp
    · simp [h, Ne.symm h]
  | cons e es ih =>
    funext k'
    simp only [setR]
    by_cases hle : go.GoStringLe k e.key'
    · simp only [hle, if_true]
      by_cases he : e.key' = k
      · simp only [he, if_true, absStore_cons, Store.set]
        by_cases h : k' = k
        · subst h; simp
        · simp [h, Ne.symm h]
      · simp only [he, if_false, absStore_cons, Store.set]
        by_cases h : k' = k
        · subst h; simp
        · simp [h, Ne.symm h]
    · simp only [hle, if_false, absStore_cons, ih, Store.set]
      have hne : e.key' ≠ k := fun h => hle (Or.inl h.symm)
      by_cases h : k' = k
      · subst h; simp [hne]
      · simp [h]

/-- **`set` writes the store.** -/
theorem absStore_setL (es : List kvEntry) (k v : GoString) :
    absStore (setL es k v) = (absStore es).set k v := by
  rw [setL_eq]; exact absStore_setR k v es

/-- `insertSorted`, recursively. -/
def insR (e : kvEntry) : List kvEntry → List kvEntry
  | [] => [e]
  | x :: xs => if entryLessB x e = false then e :: x :: xs else x :: insR e xs

theorem insStep_done_foldl (e : kvEntry) (es out : List kvEntry) :
    es.foldl (insStep e) (out, true) = (out ++ es, true) := by
  induction es generalizing out with
  | nil => simp
  | cons x es ih =>
    simp only [List.foldl_cons, insStep, Bool.true_eq_false, false_and, if_false]
    rw [ih]; simp

theorem insertSortedL_foldl (e : kvEntry) (es out : List kvEntry) :
    insFin e (es.foldl (insStep e) (out, false)) = out ++ insR e es := by
  induction es generalizing out with
  | nil => simp [insR, insFin]
  | cons x es ih =>
    simp only [List.foldl_cons]
    by_cases hl : entryLessB x e = false
    · have hs : insStep e (out, false) x = (out ++ [e, x], true) := by
        rw [insStep, if_pos (⟨rfl, hl⟩ : (out, false).2 = false ∧ entryLessB x e = false)]
      rw [hs, insStep_done_foldl, insR, if_pos hl]; simp [insFin]
    · have hs : insStep e (out, false) x = (out ++ [x], false) := by
        rw [insStep, if_neg (fun h => hl h.2)]
      rw [hs, ih, insR, if_neg hl]; simp

theorem insR_perm (e : kvEntry) (es : List kvEntry) : (insR e es).Perm (e :: es) := by
  induction es with
  | nil => exact List.Perm.refl _
  | cons x xs ih =>
    simp only [insR]
    split
    · exact List.Perm.refl _
    · exact ((ih.cons x).trans (List.Perm.swap e x xs))

/-- **`insertSorted` adds `e`** (in some order). -/
theorem insertSortedL_perm (es : List kvEntry) (e : kvEntry) :
    (insertSortedL es e).Perm (e :: es) := by
  have := insertSortedL_foldl e es []
  simp only [List.nil_append] at this
  unfold insertSortedL
  rw [this]; exact insR_perm e es

theorem perm_getElem_cons_removeAt {α : Type} (l : List α) (i : Nat) (h : i < l.length) :
    l.Perm (l[i] :: (l.take i ++ l.drop (i + 1))) := by
  have e2 : l.drop i = l[i] :: l.drop (i + 1) := List.drop_eq_getElem_cons h
  have e3 : l.take i ++ l[i] :: l.drop (i + 1) = l := by
    rw [← e2]; exact List.take_append_drop i l
  have hm := @List.perm_middle _ l[i] (l.take i) (l.drop (i + 1))
  rw [e3] at hm
  exact hm

/-- A get's step: nothing changes, and the output is an error or the store's value. -/
theorem cstep_get_inv {c c₁ : Cfg GoString GoString} {k : GoString} {o : KVOut GoString}
    (h : CStep c (.get k) o c₁) : c₁ = c ∧ (o = .err ∨ o = .okGet (c.kv k)) := by
  generalize hi : (KVIn.get k : KVIn GoString GoString) = i at h
  cases h with
  | putOk => cases hi
  | putErr => cases hi
  | getOk => cases hi; exact ⟨rfl, Or.inr rfl⟩
  | getErr => exact ⟨rfl, Or.inl rfl⟩

theorem pendAt_eq (g : GCfg) (i : Nat) (hi : i < g.pend.length) : pendAt g i = g.pend[i] := by
  unfold pendAt; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; rfl

section generic
variable {K V : Type} [DecidableEq K] [DecidableEq V]

/-- `List.perm_cons_erase` at the model's instance of `BEq (K × V)`. -/
theorem pend_perm_cons_erase {l : List (K × V)} {a : K × V} (h : a ∈ l) :
    l.Perm (a :: l.erase a) := List.perm_cons_erase h

end generic

/-- `succAt g i` is reached from `g`: its pending put takes effect. -/
theorem reach_succAt (g : GCfg) (i : Nat) (hi : i < g.pend.length) :
    Reach (absCfg g) (absCfg (succAt g i)) := by
  have hpi : pendAt g i = g.pend[i] := pendAt_eq g i hi
  have hm : toPair (pendAt g i) ∈ (absCfg g).pend := by
    unfold absCfg; rw [hpi]; exact List.mem_map_of_mem (List.getElem_mem hi)
  refine .step (.apply _ _ _ hm) (CfgEquiv.reach ⟨?_, ?_⟩)
  · simp only [absCfg, succAt, toPair]; rw [absStore_setL]
  · -- the pending puts: `erase` of the first equal pair, `removeAt` of the `i`-th
    simp only [absCfg, succAt, removeAtL, List.map_append]
    have hl : (g.pend.map toPair).length = g.pend.length := List.length_map _
    have h1 := perm_getElem_cons_removeAt (g.pend.map toPair) i (by rw [hl]; exact hi)
    have h2 := pend_perm_cons_erase (K := GoString) (V := GoString) hm
    simp only [absCfg] at h2
    rw [List.getElem_map, ← hpi] at h1
    rw [List.map_take, List.map_drop]
    exact List.Perm.cons_inv (h2.symm.trans h1)

/-! ## `closure`: a closed list -/

/-- A list whose configurations' successors are in it is closed. -/
theorem closed_of_succ (out : List GCfg)
    (hs : ∀ g ∈ out, ∀ i < g.pend.length, succAt g i ∈ out) : GClosed out := by
  intro g hg c hr
  suffices H : ∀ a b, Reach a b → ∀ g ∈ out, CfgEquiv (absCfg g) a →
      ∃ g' ∈ out, CfgEquiv (absCfg g') b from H _ _ hr g hg (CfgEquiv.refl _)
  intro a b hr
  induction hr with
  | refl => exact fun g hg he => ⟨g, hg, he⟩
  | @step c₀ c₁ c₂ hs1 _ ih =>
    intro g hg he
    cases hs1 with
    | apply k v hm =>
      -- the pending put `(k, v)` is `g`'s `i`-th
      have hm' : (k, v) ∈ g.pend.map toPair := he.2.mem_iff.2 hm
      obtain ⟨i, hi, hgi⟩ := List.getElem_of_mem hm'
      rw [List.length_map] at hi
      have hpi : toPair (pendAt g i) = (k, v) := by
        rw [pendAt_eq g i hi, ← hgi, List.getElem_map]
      refine ih (succAt g i) (hs g hg i hi) ⟨?_, ?_⟩
      · simp only [absCfg, succAt]
        rw [absStore_setL]
        simp only [toPair, Prod.mk.injEq] at hpi
        rw [hpi.1, hpi.2]
        have := he.1; simp only [absCfg] at this; rw [this]
      · -- `removeAt` of the `i`-th is `erase` of `(k, v)`, up to order
        simp only [absCfg, succAt, removeAtL]
        have hl : (g.pend.map toPair).length = g.pend.length := List.length_map _
        have h1 := perm_getElem_cons_removeAt (g.pend.map toPair) i (by rw [hl]; exact hi)
        have hpi' : toPair g.pend[i] = (k, v) := by rw [← pendAt_eq g i hi]; exact hpi
        rw [List.getElem_map, hpi'] at h1
        have h2 := pend_perm_cons_erase (K := GoString) (V := GoString) hm
        have h3 : (g.pend.map toPair).Perm c₀.pend := he.2
        rw [List.map_append, List.map_take, List.map_drop]
        exact List.Perm.cons_inv (h1.symm.trans (h3.trans h2))
    | perm p hp =>
      exact ih g hg ⟨he.1, he.2.trans hp.symm⟩

/-- A configuration's lengths, bounded by `n` (for `set`'s and `insertSorted`'s premise). -/
def Bounded (n : Nat) (g : GCfg) : Prop := g.kv.length + g.pend.length < n

theorem length_setR_le (k v : GoString) (es : List kvEntry) :
    (setR k v es).length ≤ es.length + 1 := by
  induction es with
  | nil => simp [setR]
  | cons e es ih =>
    simp only [setR]
    split
    · split <;> simp
    · simp only [List.length_cons]; omega

theorem length_setL_le (es : List kvEntry) (k v : GoString) :
    (setL es k v).length ≤ es.length + 1 := by
  rw [setL_eq]; exact length_setR_le k v es

theorem length_removeAtL (es : List kvEntry) (i : Nat) (h : i < es.length) :
    (removeAtL es i).length = es.length - 1 := by
  simp only [removeAtL, List.length_append, List.length_take, List.length_drop]
  omega

/-- A configuration `closure` pushes is no longer than its parent. -/
theorem bounded_succAt (n : Nat) (g : GCfg) (i : Nat) (hb : Bounded n g)
    (hi : i < g.pend.length) : Bounded n (succAt g i) := by
  unfold Bounded at hb ⊢
  have h1 := length_setL_le g.kv (pendAt g i).key' (pendAt g i).val'
  have h2 := length_removeAtL g.pend i hi
  simp only [succAt]
  omega

theorem succsUpTo_succ (g : GCfg) (j : Nat) :
    succsUpTo g (j + 1) = succsUpTo g j ++ [succAt g j] := by
  simp [succsUpTo, List.range_succ]

theorem mem_succsUpTo (g h : GCfg) (j : Nat) :
    h ∈ succsUpTo g j ↔ ∃ i < j, succAt g i = h := by
  simp [succsUpTo]

/-- `closure`'s loop invariant, on `out` and `work` (see `closure.lean`). -/
def CloInv (gs : List GCfg) (n : Nat) (out work : List GCfg) : Prop :=
  (∀ g ∈ out ++ work, (∃ g₀ ∈ gs, Reach (absCfg g₀) (absCfg g)) ∧ Bounded n g) ∧
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
theorem cloInv_add (gs : List GCfg) (n : Nat) (out work : List GCfg) (h : GCfg)
    (hI : CloInv gs n out (work ++ [h])) (hm : h ∉ out) :
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
      exact ⟨⟨g₀, hg₀, hr.trans (reach_succAt h i hi)⟩, bounded_succAt n h i hb hi⟩
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
theorem cloInv_done (gs : List GCfg) (n : Nat) (out : List GCfg) (hI : CloInv gs n out []) :
    ClosureOk gs out ∧ GClosed out ∧ ∀ g ∈ out, Bounded n g := by
  obtain ⟨h1, h2, h3⟩ := hI
  simp only [List.append_nil] at h1 h2 h3
  have hc : GClosed out := closed_of_succ out h3
  exact ⟨⟨fun g hg => (h1 g hg).1, fun g₀ hg₀ c hr => hc g₀ (h2 g₀ hg₀) c hr⟩, hc,
    fun g hg => (h1 g hg).2⟩

/-- The representation of a closed list is closed. -/
theorem setOf_closed {gs : List GCfg} (hc : GClosed gs) : (setOf gs).Closed := by
  rintro c c' ⟨g, hg, he⟩ hr
  exact hc g hg c' (he.reach.trans hr)

/-! ## `step` -/

theorem lookupL_absStore (es : List kvEntry) (k : GoString) :
    absStore es k = if (lookupL es k).2 = true then some (lookupL es k).1 else none := by
  unfold absStore lookupL
  cases es.find? (fun e => decide (e.key' = k)) <;> simp

/-- `lookup` returns at the first entry of the key. -/
theorem lookupL_found (es : List kvEntry) (k : GoString) (j : Nat) (e : kvEntry)
    (hj : es[j]? = some e) (hpre : ∀ x ∈ es.take j, x.key' ≠ k) (he : e.key' = k) :
    lookupL es k = (e.val', true) := by
  have hl : j < es.length := by
    rcases Nat.lt_or_ge j es.length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at hj; cases hj
  have hsplit : es = es.take j ++ e :: es.drop (j + 1) := by
    rw [List.getElem?_eq_getElem hl] at hj
    have := List.drop_eq_getElem_cons hl
    rw [Option.some.inj hj] at this
    rw [← this, List.take_append_drop]
  have hn : (es.take j).find? (fun e => decide (e.key' = k)) = none := by
    rw [List.find?_eq_none]; intro x hx; simpa using hpre x hx
  unfold lookupL
  rw [hsplit, List.find?_append, hn, Option.none_or, List.find?_cons_of_pos (by simpa using he)]

/-- `lookup` returns no value when no entry has the key. -/
theorem lookupL_none (es : List kvEntry) (k : GoString) (h : ∀ x ∈ es, x.key' ≠ k) :
    lookupL es k = (go!"", false) := by
  have hn : es.find? (fun e => decide (e.key' = k)) = none := by
    rw [List.find?_eq_none]; intro x hx; simpa using h x hx
  unfold lookupL; rw [hn]

/-- A step lengthens a configuration by at most one entry. -/
theorem stepL_bounded (n : Nat) (g : GCfg) (x : Input) (y : Output) (hb : Bounded n g)
    (g' : GCfg) (hg' : g' ∈ stepL g x y) : Bounded (n + 1) g' := by
  unfold Bounded at hb ⊢
  unfold stepL at hg'
  have hins := (insertSortedL_perm g.pend ⟨x.Key', x.Val'⟩).length_eq
  have hset := length_setL_le g.kv x.Key' x.Val'
  simp only [List.length_cons] at hins
  split at hg'
  · split at hg'
    · simp only [List.mem_singleton] at hg'; subst hg'; simp only; omega
    · split at hg'
      · cases hg'
      · simp only [List.mem_singleton] at hg'; subst hg'; simp only; omega
  · split at hg'
    · simp only [List.mem_singleton] at hg'; subst hg'; omega
    · simp only at hg'
      split at hg'
      · cases hg'
      · simp only [List.mem_singleton] at hg'; subst hg'; omega

/-- A configuration's step by `stepL` is a `CStep` of its model configuration. -/
theorem stepL_sound (g : GCfg) (x : Input) (y : Output) (i : KVIn GoString GoString)
    (o : KVOut GoString) (hd : decIO x y = some (i, o)) (g' : GCfg) (hg' : g' ∈ stepL g x y) :
    ∃ c₁, CStep (absCfg g) i o c₁ ∧ CfgEquiv c₁ (absCfg g') := by
  unfold decIO at hd
  unfold stepL at hg'
  by_cases hp : x.Put' = true
  · simp only [hp, if_true] at hd hg'
    by_cases he : y.Err' = true
    · simp only [he, if_true, Option.some.injEq, Prod.mk.injEq, List.mem_singleton] at hd hg'
      obtain ⟨rfl, rfl⟩ := hd
      subst hg'
      refine ⟨_, .putErr _ _ _, rfl, ?_⟩
      simp only [absCfg]
      have := (insertSortedL_perm g.pend ⟨x.Key', x.Val'⟩).map toPair
      exact this.symm
    · simp only [he, Bool.false_eq_true, if_false] at hd hg'
      by_cases hf : y.Found' = false ∧ y.Val' = go!""
      · simp only [hf, and_self, if_true, Option.some.injEq, Prod.mk.injEq] at hd
        obtain ⟨rfl, rfl⟩ := hd
        have hn : ¬ (y.Found' = true ∨ y.Val' ≠ go!"") := by
          rw [hf.1, hf.2]; simp
        simp only [hn, if_false, List.mem_singleton] at hg'
        subst hg'
        refine ⟨_, .putOk _ _ _, ?_, List.Perm.refl _⟩
        simp only [absCfg]; rw [absStore_setL]
      · simp only [hf, if_false] at hd; cases hd
  · simp only [hp, Bool.false_eq_true, if_false] at hd hg'
    by_cases he : y.Err' = true
    · simp only [he, if_true, Option.some.injEq, Prod.mk.injEq, List.mem_singleton] at hd hg'
      obtain ⟨rfl, rfl⟩ := hd
      subst g'
      exact ⟨_, .getErr _ _, CfgEquiv.refl _⟩
    · simp only [he, Bool.false_eq_true, if_false] at hd hg'
      split at hg'
      · cases hg'
      · next hacc =>
        simp only [List.mem_singleton] at hg'
        subst g'
        -- the get's output is the store's value
        have hv : o = .okGet (absStore g.kv x.Key') ∧ i = .get x.Key' := by
          rw [lookupL_absStore]
          by_cases hf : y.Found' = true
          · simp only [hf, if_true, Option.some.injEq, Prod.mk.injEq] at hd
            obtain ⟨rfl, rfl⟩ := hd
            have : (lookupL g.kv x.Key').2 = true ∧ (lookupL g.kv x.Key').1 = y.Val' := by
              refine Classical.byContradiction fun hc => ?_
              apply hacc
              by_cases h2 : (lookupL g.kv x.Key').2 = true
              · exact Or.inr (Or.inl ⟨h2, fun h => hc ⟨h2, h⟩⟩)
              · exact Or.inl (by rw [hf]; exact h2)
            simp [this.1, this.2]
          · simp only [hf, Bool.false_eq_true, if_false] at hd
            by_cases hv : y.Val' = go!""
            · simp only [hv, if_true, Option.some.injEq, Prod.mk.injEq] at hd
              obtain ⟨rfl, rfl⟩ := hd
              have : (lookupL g.kv x.Key').2 = false := by
                refine Classical.byContradiction fun hc => ?_
                apply hacc
                exact Or.inl (by simp only [Bool.not_eq_false] at hc; rw [hc]; simpa using hf)
              simp [this]
            · simp only [hv, if_false] at hd; cases hd
        obtain ⟨rfl, rfl⟩ := hv
        exact ⟨_, .getOk _ _, CfgEquiv.refl _⟩

/-- A `CStep` of a configuration equivalent to `g`'s is one of `stepL g`, up to equivalence. -/
theorem stepL_complete (g : GCfg) (x : Input) (y : Output) (i : KVIn GoString GoString)
    (o : KVOut GoString) (hd : decIO x y = some (i, o)) (c c₁ : Cfg GoString GoString)
    (he : CfgEquiv (absCfg g) c) (hs : CStep c i o c₁) :
    ∃ g' ∈ stepL g x y, CfgEquiv (absCfg g') c₁ := by
  unfold decIO at hd
  unfold stepL
  by_cases hp : x.Put' = true
  · simp only [hp, if_true] at hd ⊢
    by_cases hE : y.Err' = true
    · simp only [hE, if_true, Option.some.injEq, Prod.mk.injEq] at hd ⊢
      obtain ⟨rfl, rfl⟩ := hd
      cases hs
      refine ⟨_, List.mem_singleton_self _, he.1, ?_⟩
      simp only [absCfg]
      exact ((insertSortedL_perm g.pend ⟨x.Key', x.Val'⟩).map toPair).trans
        (List.Perm.cons _ he.2)
    · simp only [hE, Bool.false_eq_true, if_false] at hd ⊢
      by_cases hf : y.Found' = false ∧ y.Val' = go!""
      · simp only [hf, and_self, if_true, Option.some.injEq, Prod.mk.injEq] at hd
        obtain ⟨rfl, rfl⟩ := hd
        have hn : ¬ (y.Found' = true ∨ y.Val' ≠ go!"") := by
          rw [hf.1, hf.2]; simp
        simp only [hn, if_false]
        cases hs
        refine ⟨_, List.mem_singleton_self _, ?_, he.2⟩
        have hk : absStore g.kv = c.kv := he.1
        simp only [absCfg]; rw [absStore_setL, hk]
      · simp only [hf, if_false] at hd; cases hd
  · simp only [hp, Bool.false_eq_true, if_false] at hd ⊢
    by_cases hE : y.Err' = true
    · simp only [hE, if_true, Option.some.injEq, Prod.mk.injEq] at hd ⊢
      obtain ⟨rfl, rfl⟩ := hd
      cases hs
      exact ⟨_, List.mem_singleton_self _, he⟩
    · simp only [hE, Bool.false_eq_true, if_false] at hd ⊢
      have hk : c.kv = absStore g.kv := he.1.symm
      by_cases hf : y.Found' = true
      · simp only [hf, if_true, Option.some.injEq, Prod.mk.injEq] at hd
        obtain ⟨rfl, rfl⟩ := hd
        obtain ⟨hc1, ho⟩ := cstep_get_inv hs
        subst c₁
        have hv : some y.Val' = c.kv x.Key' := by
          rcases ho with ho | ho
          · cases ho
          · exact KVOut.okGet.inj ho
        · -- `c.kv x.Key' = some y.Val'`
          have h2 := lookupL_absStore g.kv x.Key'
          rw [← hk] at h2
          rw [h2] at hv
          split at hv
          · next hl =>
            simp only [Option.some.injEq] at hv
            have hacc : ¬ ((lookupL g.kv x.Key').2 ≠ y.Found' ∨
                ((lookupL g.kv x.Key').2 = true ∧ (lookupL g.kv x.Key').1 ≠ y.Val') ∨
                ((lookupL g.kv x.Key').2 = false ∧ y.Val' ≠ go!"")) := by
              simp [hl, hf, hv]
            simp only [hacc, if_false]
            exact ⟨_, List.mem_singleton_self _, he⟩
          · cases hv
      · simp only [hf, Bool.false_eq_true, if_false] at hd
        by_cases hV : y.Val' = go!""
        · simp only [hV, if_true, Option.some.injEq, Prod.mk.injEq] at hd
          obtain ⟨rfl, rfl⟩ := hd
          obtain ⟨hc1, ho⟩ := cstep_get_inv hs
          subst c₁
          have hv : none = c.kv x.Key' := by
            rcases ho with ho | ho
            · cases ho
            · exact KVOut.okGet.inj ho
          · have h2 := lookupL_absStore g.kv x.Key'
            rw [← hk] at h2
            rw [h2] at hv
            split at hv
            · cases hv
            · next hl =>
              have hacc : ¬ ((lookupL g.kv x.Key').2 ≠ y.Found' ∨
                  ((lookupL g.kv x.Key').2 = true ∧ (lookupL g.kv x.Key').1 ≠ y.Val') ∨
                  ((lookupL g.kv x.Key').2 = false ∧ y.Val' ≠ go!"")) := by
                simp only [Bool.not_eq_true] at hl hf
                simp [hl, hf, hV]
              simp only [hacc, if_false]
              exact ⟨_, List.mem_singleton_self _, he⟩
        · simp only [hV, if_false] at hd; cases hd

/-- An operation the decoder rejects has no step. -/
theorem stepL_none (g : GCfg) (x : Input) (y : Output) (hd : decIO x y = none) :
    stepL g x y = [] := by
  unfold decIO at hd
  unfold stepL
  by_cases hp : x.Put' = true
  · simp only [hp, if_true] at hd ⊢
    by_cases hE : y.Err' = true
    · simp [hE] at hd
    · simp only [hE, Bool.false_eq_true, if_false] at hd ⊢
      by_cases hf : y.Found' = false ∧ y.Val' = go!""
      · simp [hf] at hd
      · have : y.Found' = true ∨ y.Val' ≠ go!"" := by
          by_cases h1 : y.Found' = true
          · exact Or.inl h1
          · exact Or.inr (fun h2 => hf ⟨by simpa using h1, h2⟩)
        simp [this]
  · simp only [hp, Bool.false_eq_true, if_false] at hd ⊢
    by_cases hE : y.Err' = true
    · simp [hE] at hd
    · simp only [hE, Bool.false_eq_true, if_false] at hd ⊢
      by_cases hf : y.Found' = true
      · simp [hf] at hd
      · by_cases hV : y.Val' = go!""
        · simp [hf, hV] at hd
        · have : (lookupL g.kv x.Key').2 ≠ y.Found' ∨
              ((lookupL g.kv x.Key').2 = true ∧ (lookupL g.kv x.Key').1 ≠ y.Val') ∨
              ((lookupL g.kv x.Key').2 = false ∧ y.Val' ≠ go!"") := by
            cases h : (lookupL g.kv x.Key').2
            · exact Or.inr (Or.inr ⟨rfl, hV⟩)
            · exact Or.inl (by simp only [Bool.not_eq_true] at hf; rw [hf]; simp)
          simp only [this, if_true]

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

/-! ## `Step` -/

/-- **`Step`'s result** (see the file header): the `closure` `out` of `stepAllL gs x y`
represents `post S i o` and is closed. -/
theorem step_closure_ok (gs out : List GCfg) (S : KVSet GoString GoString) (x : Input)
    (y : Output) (i : KVIn GoString GoString) (o : KVOut GoString)
    (hS : GOk gs S) (hd : decIO x y = some (i, o)) (hc : ClosureOk (stepAllL gs x y) out)
    (hcl : GClosed out) : GOk out (post S i o) := by
  refine ⟨hcl, ?_⟩
  obtain ⟨hgs, rfl⟩ := hS
  funext c'
  apply propext
  constructor
  · -- a configuration of `post`: from `g₀ ∈ gs`, pending puts, the step, pending puts
    rintro ⟨c₀, c, c₁, ⟨g₀, hg₀, he₀⟩, hr₀, hs, hr₁⟩
    obtain ⟨g, hg, he⟩ := hgs g₀ hg₀ c (he₀.reach.trans hr₀)
    obtain ⟨g₁, hg₁, he₁⟩ := stepL_complete g x y i o hd c c₁ he hs
    have hm : g₁ ∈ stepAllL gs x y := (mem_stepAllL gs x y g₁).2 ⟨g, hg, hg₁⟩
    exact hc.2 g₁ hm c' (he₁.reach.trans hr₁)
  · -- a configuration of `out`: reached from a step of a configuration of `gs`
    rintro ⟨g', hg', he'⟩
    obtain ⟨g₁, hg₁, hr⟩ := hc.1 g' hg'
    obtain ⟨g, hg, hs⟩ := (mem_stepAllL gs x y g₁).1 hg₁
    obtain ⟨c₁, hcs, he₁⟩ := stepL_sound g x y i o hd g₁ hs
    exact ⟨absCfg g, absCfg g, c₁, ⟨g, hg, CfgEquiv.refl _⟩, .refl _, hcs,
      he₁.reach.trans (hr.trans he'.reach)⟩

/-- `Step`'s result is empty when the decoder rejects the operation. -/
theorem step_closure_none (gs out : List GCfg) (x : Input) (y : Output)
    (hd : decIO x y = none) (hc : ClosureOk (stepAllL gs x y) out) : out = [] := by
  cases out with
  | nil => rfl
  | cons g' out =>
    obtain ⟨g₁, hg₁, -⟩ := hc.1 g' List.mem_cons_self
    obtain ⟨g, -, hs⟩ := (mem_stepAllL gs x y g₁).1 hg₁
    rw [stepL_none g x y hd] at hs
    cases hs

/-- A representation is empty only when its list is. -/
theorem setOf_nonempty (gs : List GCfg) : (∃ c, setOf gs c) ↔ gs ≠ [] := by
  constructor
  · rintro ⟨c, g, hg, -⟩ h; subst h; cases hg
  · intro h
    cases gs with
    | nil => exact absurd rfl h
    | cons g _ => exact ⟨absCfg g, g, List.mem_cons_self, CfgEquiv.refl _⟩

/-- The initial state: one empty configuration. -/
theorem gok_init : GOk [⟨[], []⟩] (kvInit : KVSet GoString GoString) := by
  have h0 : absCfg (⟨[], []⟩ : GCfg) = ⟨fun _ => none, []⟩ := rfl
  have hset : (kvInit : KVSet GoString GoString) = setOf [⟨[], []⟩] := by
    funext c
    apply propext
    simp only [kvInit, setOf, List.mem_singleton, exists_eq_left, h0, CfgEquiv]
    constructor
    · rintro rfl; exact ⟨rfl, List.Perm.refl _⟩
    · rintro ⟨h1, h2⟩
      rw [← Cfg.eta' c, ← h1, ← List.Perm.eq_nil h2.symm]
  refine ⟨?_, hset⟩
  intro g hg c hr
  simp only [List.mem_singleton] at hg
  subst hg
  have hc : (kvInit : KVSet GoString GoString) c := kvInit_closed _ _ (by rw [h0]; rfl) hr
  refine ⟨⟨[], []⟩, List.mem_singleton_self _, ?_⟩
  rw [h0, hc]; exact CfgEquiv.refl _

end go

end linkv
end EtcdGrove
end Perennial

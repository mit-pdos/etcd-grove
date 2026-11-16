/-
Lean-first (no Rocq counterpart).

# The driver's watch check: its Go values (stage 7f-6 B1)

As `MDefs.lean` for the model's stores: the Go values of `watch.go`'s check and their models
(`KWatch.lean`):

- `wevOf w`, the model's event (`WEv`) of a Go `WEvent` (its type as a natural number);
  `wevsOwn s evs`, the Go slice `s` holds events whose models are `evs`, read-only;
- `wevsOwnM s evs`, the same owned (a fresh slice), which persists into `wevsOwn s evs`;
- `chgOf ch`, the model's change (`Chg`) of a Go `change` (the previous and current objects present
  only when `hasPrev`/`hasCur`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.MDefs
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.KWatch

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (WEvent change Obj)

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

/-- The model's event of a Go `WEvent`. -/
def wevOf (w : WEvent) : WEv := ⟨uint.nat w.Type', w.Obj'⟩

/-- The Go slice `s` holds events whose models are `evs`, read-only. -/
def wevsOwn (s : GoSlice) (evs : List WEv) : IProp GF :=
  iprop(∃ ws : List WEvent, s ↦*□ ws ∗ ⌜ws.map wevOf = evs⌝)

instance wevsOwn_persistent (s : GoSlice) (evs : List WEv) :
    Persistent (wevsOwn (GF := GF) s evs) := by
  unfold wevsOwn; infer_instance

/-- The Go slice `s` holds events whose models are `evs`, owned (a fresh slice a function returns). -/
def wevsOwnM (s : GoSlice) (evs : List WEv) : IProp GF :=
  iprop(∃ ws : List WEvent, s ↦* ws ∗ ⌜ws.map wevOf = evs⌝)

/-- The model's change of a Go `change`. -/
def chgOf (ch : change) : Chg :=
  ⟨ch.key', if ch.hasPrev' then some ch.prev' else none,
    if ch.hasCur' then some ch.cur' else none, uint.nat ch.rv'⟩

theorem wevsOwnM_persist (s : GoSlice) (evs : List WEv) :
    wevsOwnM (GF := GF) s evs ⊢ |==> wevsOwn s evs := by
  unfold wevsOwnM wevsOwn
  iintro ⟨%ws, Hs, %He⟩
  imod ownSlice_persist _ _ _ $$ Hs with #Hs
  imodintro
  iexists ws
  isplit
  · iexact Hs
  · ipureintro; exact He

theorem Obj_eq_iff (a b : Obj) : a = b ↔
    a.Namespace' = b.Namespace' ∧ a.Name' = b.Name' ∧ a.UID' = b.UID' ∧ a.Value' = b.Value' ∧
    a.Node' = b.Node' ∧ a.App' = b.App' ∧ a.ResourceVersion' = b.ResourceVersion' ∧
    a.Annotated' = b.Annotated' := by
  obtain ⟨_, _, _, _, _, _, _, _⟩ := a
  obtain ⟨_, _, _, _, _, _, _, _⟩ := b
  simp

/-- `evsEqL` pointwise. -/
theorem evsEqL_iff (a b : List WEv) : evsEqL a b = true ↔
    a.length = b.length ∧ ∀ i (ha : i < a.length) (hb : i < b.length),
      a[i].t = b[i].t ∧ a[i].o = b[i].o := by
  unfold evsEqL
  rw [decide_eq_true_iff, List.ext_getElem_iff]
  simp only [List.length_map, List.getElem_map, Prod.mk.injEq]

/-- Two event lists that differ at an index are not equal. -/
theorem evsEqL_false_of (a b : List WEv) (k : Nat) (e1 e2 : WEv) (h1 : a[k]? = some e1)
    (h2 : b[k]? = some e2) (hne : ¬(e1.t = e2.t ∧ e1.o = e2.o)) : evsEqL a b = false := by
  cases h : evsEqL a b
  · rfl
  · exfalso
    obtain ⟨hl, hi⟩ := (evsEqL_iff a b).1 h
    obtain ⟨hk1, he1⟩ := List.getElem?_eq_some_iff.1 h1
    obtain ⟨hk2, he2⟩ := List.getElem?_eq_some_iff.1 h2
    have := hi k hk1 hk2
    rw [he1, he2] at this
    exact hne this

theorem wevOf_ne_type (w w2 : WEvent) (h : ¬ w.Type' = w2.Type') :
    ¬((wevOf w).t = (wevOf w2).t ∧ (wevOf w).o = (wevOf w2).o) := by
  simp only [wevOf]
  intro ⟨ht, _⟩
  exact h (by word)

theorem wevOf_ne_obj (w w2 : WEvent) (h : ¬ w.Obj' = w2.Obj') :
    ¬((wevOf w).t = (wevOf w2).t ∧ (wevOf w).o = (wevOf w2).o) := by
  simp only [wevOf]
  intro ⟨_, ho⟩
  exact h ho

theorem bmStepL_none_foldl (es : List WEv) : es.foldl bmStepL none = none := by
  induction es with
  | nil => rfl
  | cons e es ih => simpa [List.foldl_cons, bmStepL] using ih

/-- `bookmarksOkL` stops at the first event its step rejects. -/
theorem bookmarksOkL_false_of (evs : List WEv) (k : Nat) (e : WEv) (st : Nat × Nat × Bool)
    (hk : evs[k]? = some e) (hst : (evs.take k).foldl bmStepL (some (0, 0, false)) = some st)
    (hn : bmStepL (some st) e = none) : bookmarksOkL evs = false := by
  unfold bookmarksOkL
  rw [← List.take_append_drop (k + 1) evs, List.foldl_append, List.take_add_one, hk,
    Option.toList_some, List.foldl_append, hst, List.foldl_cons, List.foldl_nil, hn,
    bmStepL_none_foldl]
  rfl

/-- `bmStepL` on a Go event, in the Go code's comparisons. -/
theorem bmStepL_wev (lb le : w64) (ann : Bool) (w : WEvent) :
    bmStepL (some (uint.nat lb, uint.nat le, ann)) (wevOf w) =
      if w.Type' = W64 3 then
        if uint.Z w.Obj'.ResourceVersion' < uint.Z lb ∨ uint.Z w.Obj'.ResourceVersion' < uint.Z le
        then none
        else if w.Obj'.Annotated' then
          (if ann then none else some (uint.nat w.Obj'.ResourceVersion', uint.nat le, true))
        else some (uint.nat w.Obj'.ResourceVersion', uint.nat le, ann)
      else if uint.Z w.Obj'.ResourceVersion' ≤ uint.Z lb then none
      else some (uint.nat lb, uint.nat (if uint.Z le < uint.Z w.Obj'.ResourceVersion'
        then w.Obj'.ResourceVersion' else le), ann) := by
  have h3 : uint.nat w.Type' = 3 ↔ w.Type' = W64 3 := by
    constructor
    · intro h; word
    · intro h; rw [h]; rfl
  simp only [bmStepL, wevOf, h3]
  by_cases hT : w.Type' = W64 3
  · simp only [hT, ↓reduceIte]
    by_cases hc : uint.Z w.Obj'.ResourceVersion' < uint.Z lb ∨ uint.Z w.Obj'.ResourceVersion' < uint.Z le
    · have : uint.nat w.Obj'.ResourceVersion' < uint.nat lb ∨
          uint.nat w.Obj'.ResourceVersion' < uint.nat le := by word
      simp only [hc, this, ↓reduceIte]
    · have : ¬ (uint.nat w.Obj'.ResourceVersion' < uint.nat lb ∨
          uint.nat w.Obj'.ResourceVersion' < uint.nat le) := by word
      simp only [hc, this, ↓reduceIte]
      rfl
  · simp only [hT, ↓reduceIte]
    by_cases hc : uint.Z w.Obj'.ResourceVersion' ≤ uint.Z lb
    · have : uint.nat w.Obj'.ResourceVersion' ≤ uint.nat lb := by word
      simp only [hc, this, ↓reduceIte]
    · have : ¬ uint.nat w.Obj'.ResourceVersion' ≤ uint.nat lb := by word
      simp only [hc, this, ↓reduceIte, Option.some.injEq, Prod.mk.injEq, _root_.true_and,
        _root_.and_true]
      by_cases hl : uint.Z le < uint.Z w.Obj'.ResourceVersion'
      · simp only [hl, ↓reduceIte]; word
      · simp only [hl, ↓reduceIte]; word

end defs

end k8s_etcd3
end EtcdGrove
end Perennial

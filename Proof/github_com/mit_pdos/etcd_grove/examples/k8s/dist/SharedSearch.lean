/-
Lean-first (no Rocq counterpart).

# k8s-dist K4: `SharedModel`'s full mode as a search, and the completeness statement

`notes/k8s-dist-k4.md` §2. Per operation `(x, y)` and configuration `c`, the full mode (`SharedModel.Step`
with `Full`, `examples/k8s/etcd3/export.go`): `settle` (each pending write, in any order, dropped if it
has no effect on the store, or landed at one of `landings`: the store skipped to the landing less one,
then the write's step), `skipTo(target(x, y, rv))`, then `Model`'s step (`stepL`). Here:

- `skipToL`: `skipTo`, as foreign steps (`SharedSem.lean`);
- `targetL`: `target`, with G7 (`152e1a4634`: a watch-list with an event needs the configuration at its
  resource version, at least 1) and G8 (K4-3: a write's target does not depend on its `MinRV`
  parsing) and G10 (K4-3: every kind `mstepL` answers with `mgetL`, not only `KGet`, needs its
  `MinRV`); `notes/k8s-dist-k4.md`, "K4-3: more gaps";
- `SettleL A`: `settle`'s reachable configurations, with the landings `landingsFull A [] [] rv`
  (`SharedPlace.lean`): the next revision and every anchor at or above `rv` and the one after it. The
  Go landings add the key's shown revisions and the answer's own one, so the Go search's
  configurations include these (K9);
- `SearchRun A c ops`: a run of the search, one configuration per step;
- **`FullComplete`**: K4's theorem, as a statement (proved in a later stage): every run of the semantic
  model from the seeded store passes the search, for any anchor list that names every revision the
  history shows (`AnchorsOk`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.dist.SharedSem
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.dist.SharedPlace

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_dist

open k8s_etcd3
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Input Output Obj)

section go
variable [GooseExts]

/-- **`skipTo(c, t)`**: `h` at the revision `t` by foreign revisions, or `h` if it is at `t` or
beyond. (Go's `skipTo` numbers the appended stores by the history's length, which is the revision on
every configuration the search reaches.) -/
def skipToL (h : HSt) (t : Nat) : HSt := Nat.repeat foreignL (t - uint.nat h.st.rv) h

/-- The greatest revision among a watch's events other than errors (0 if none). -/
def evMaxL (evs : List WEv) : Nat :=
  (evs.filter fun e => e.t < 4).foldl (fun t e => max t (uint.nat e.o.ResourceVersion')) 0

/-- **`target(in, out, rv)`** (with G7): the least revision a configuration at `rv` must be at for `x`
to answer `y` (0: none). A watch: the greatest revision its events and bookmarks name, and for a
watch-list with an event, also its resource version, at least 1. A "not found": its revision. A
successful List: its past read's revision or its current revision; a Get: its minimum resource
version; a write answering a revision above `rv`: the one before it. -/
def targetL (x : Input) (y : Output) (rv : Nat) : Nat :=
  if x.Kind' = W64 5 then
    if y.WFailed' || x.Skip' then 0
    else match decWEventsL y.WEvents' with
      | none => 0
      | some evs =>
        if x.SendInit' = W64 2 ∧ evs.any (fun e => e.t < 4) then
          match parseRVD x.MinRV' with
          | some req => max (evMaxL evs) (max (uint.nat req) 1)
          | none => evMaxL evs
        else evMaxL evs
  else if y.Err' = W64 1 then uint.nat y.ErrRV'
  else if y.Err' ≠ W64 0 then 0
  else if x.Kind' = W64 4 then
    match parseRVD x.MinRV' with
    | none => 0
    | some req => if pastReadL x req then uint.nat req else uint.nat y.ListRV'
  else if x.Kind' = W64 0 ∨ x.Kind' = W64 1 ∨ x.Kind' = W64 2 then
    (if rv < uint.nat y.RV' then uint.nat y.RV' - 1 else 0)
  else
    match parseRVD x.MinRV' with
    | none => 0
    | some req => uint.nat req

/-- **`settle`'s configurations** from `c`, with the full mode's landings over the anchors `A`: the
`i`-th pending write is dropped if it has no effect on the store (`mstepL` keeps its revision), or
lands at a landing `l` (the store skipped to `l - 1`, then the write's step); any number of times. -/
inductive SettleL (A : List Nat) : GCfg → GCfg → Prop where
  | refl (c : GCfg) : SettleL A c c
  | drop {c d : GCfg} (i : Nat) : i < c.pend.length →
      (mstepL (pendAt c i) c.st.st).1.rv = c.st.st.rv →
      SettleL A ⟨c.st, removeAtL c.pend i⟩ d → SettleL A c d
  | land {c d : GCfg} (i l : Nat) : i < c.pend.length →
      (mstepL (pendAt c i) c.st.st).1.rv ≠ c.st.st.rv →
      l ∈ landingsFull A [] [] (uint.nat c.st.st.rv) →
      SettleL A ⟨(kstepL (pendAt c i) (skipToL c.st (l - 1))).1, removeAtL c.pend i⟩ d →
      SettleL A c d

/-- **One step of the full mode** from `c` on the operation `(x, y)`: a configuration `settle` reaches,
skipped to the target, then `Model`'s step. -/
def SearchStep (A : List Nat) (c : GCfg) (x : Input) (y : Output) (e : GCfg) : Prop :=
  ∃ d, SettleL A c d ∧ e ∈ stepL ⟨skipToL d.st (targetL x y (uint.nat d.st.st.rv)), d.pend⟩ x y

/-- **A run of the full mode's search** over the operations `ops`: a configuration per step. -/
inductive SearchRun (A : List Nat) : GCfg → List (Input × Output) → Prop where
  | nil (c : GCfg) : SearchRun A c []
  | cons {c e : GCfg} {x : Input} {y : Output} {ops : List (Input × Output)} :
      SearchStep A c x y e → SearchRun A e ops → SearchRun A c ((x, y) :: ops)

/-- **The revisions one operation names** are anchors (`HistoryRevs`, `notes/k8s-dist-k4.md` §2):
its minimum resource version and resource-version precondition (where they parse); an answer's error
revision and list revision, a successful answer's object's revision (with or without a name: G9, `notes/k8s-dist-k4.md`, "K4-3: more
gaps"); the revisions of a
successful list's items, of a watch's events and bookmarks (not its errors), and of the object a failed
resource-version precondition's message names (Go's `rvOfMsg`). -/
def OpAnchors (A : List Nat) (x : Input) (y : Output) : Prop :=
  (∀ r, parseRVD x.MinRV' = some r → uint.nat r ∈ A) ∧
  (∀ r, x.HasPreRV' = true → parseRVD x.PreRV' = some r → uint.nat r ∈ A) ∧
  (x.Kind' = W64 5 → y.WFailed' = false → ∀ evs, decWEventsL y.WEvents' = some evs → ∀ e ∈ evs,
    e.t ≠ 4 → uint.nat e.o.ResourceVersion' ∈ A) ∧
  (x.Kind' ≠ W64 5 →
    uint.nat y.ErrRV' ∈ A ∧ uint.nat y.ListRV' ∈ A ∧
    (y.Err' = W64 0 → uint.nat y.RV' ∈ A) ∧
    (x.Kind' = W64 4 → y.Err' = W64 0 → ∀ os : List Obj, y.Items' = encItemsL os → ∀ o ∈ os,
      uint.nat o.ResourceVersion' ∈ A) ∧
    (∀ o : Obj, y.ErrMsg' = preMsgL x o → (x.HasPreUID' && !decide (x.PreUID' = o.UID')) = false →
      uint.nat o.ResourceVersion' ∈ A))

/-- Every operation of `ops` names only anchors, and 0 is one (harmless: no landing is added). -/
def AnchorsOk (A : List Nat) (ops : List (Input × Output)) : Prop :=
  0 ∈ A ∧ ∀ p ∈ ops, OpAnchors A p.1 p.2

/-- **K4's theorem, as a statement**: from a seeded store `h0` whose history has a store per revision,
every run of the semantic model over `ops` is a run of the full mode's search, for anchors naming every
revision the history shows. (Proved in a later stage: `notes/k8s-dist-k4.md`, "Handoff K4-2".) -/
def FullComplete : Prop :=
  ∀ (h0 : HSt) (A : List Nat) (ops : List (Input × Output)) (c' : GCfg),
    h0.hist.length = uint.nat h0.st.rv → (∀ v ≤ uint.nat h0.st.rv, v ∈ A) →
    AnchorsOk A ops → SRun h0 ⟨h0, []⟩ ops c' → SearchRun A ⟨h0, []⟩ ops

/-! ## `skipToL` -/

theorem skipToL_le (h : HSt) (t : Nat) (ht : t ≤ uint.nat h.st.rv) : skipToL h t = h := by
  simp [skipToL, Nat.sub_eq_zero_of_le ht, Nat.repeat]

theorem repeat_foreignL_items (n : Nat) (h : HSt) : (Nat.repeat foreignL n h).st.items = h.st.items := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Nat.repeat]; rw [foreignL_items, ih]

theorem skipToL_items (h : HSt) (t : Nat) : (skipToL h t).st.items = h.st.items :=
  repeat_foreignL_items _ _

theorem repeat_foreignL_rv (n : Nat) (h : HSt) (hw : uint.nat h.st.rv + n < 2 ^ 64) :
    uint.nat (Nat.repeat foreignL n h).st.rv = uint.nat h.st.rv + n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [Nat.repeat]
    rw [foreignL_rv _ (by rw [ih (by omega)]; omega), ih (by omega)]; omega

/-- `skipToL` reaches the target (below `2^64`), or stays above it. -/
theorem skipToL_rv (h : HSt) (t : Nat) (ht : t < 2 ^ 64) :
    uint.nat (skipToL h t).st.rv = max (uint.nat h.st.rv) t := by
  by_cases hle : t ≤ uint.nat h.st.rv
  · rw [skipToL_le h t hle]; omega
  · unfold skipToL
    rw [repeat_foreignL_rv _ _ (by omega)]; omega

end go

end k8s_dist
end EtcdGrove
end Perennial

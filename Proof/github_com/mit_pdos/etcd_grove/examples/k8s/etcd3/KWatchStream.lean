/-
Lean-first (no Rocq counterpart).

# The watch check accepts the watches the store delivers (stage 7f-2 of `notes/k8s-7f-scope.md`)

What a watch of the etcd3 store delivers, stated over the store's history `hs` (the store at each
revision, `hs[R-1]` at `R`), and the obligation behind the driver's closed theorem with watches:
**`watchOkL_of_stream`**, the driver's check (`watchOkL`, `KWatch.lean`) accepts every such watch
against the configuration whose history is `hs` (the real one, 7e's invariant).

- `TailOk x hs c es`: the events `es` of a watch of `x` from the cursor `c` (the last revision it
  reported): change events in revision order, none missing (`evAtL`), and progress bookmarks at
  revisions with no change in scope since the cursor;
- `StreamOkL x req hs evs`: the events a watch delivered, Error events anywhere (the etcd3 watcher
  can send events after one, `nonissues/k8s-etcd3-watcher-events-after-error.md`): for a
  watch-list, the initial events at some revision `r0 ≥ req` (all of them followed by the
  initial-events-end bookmark at `r0` and a tail from `r0`, or a prefix of them if the watch
  ended before); otherwise a tail from the requested revision (any, for RV 0: the store's
  current one when the watch started);
- `HistWf x hs`: what the model's histories satisfy (the objects carry their revisions, no
  annotation, revisions below `2^63`), a premise here, proved of the model's histories in 7f-6.

The store's watch spec (7f-5a) delivers `StreamOkL` over etcd's history read as stores; 7e's
invariant identifies that with the matching configuration's `hist`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.KWatch

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Obj Input Output item)

section go
variable [GooseExts]

/-- A watch's events from the cursor `c` (see the file header). -/
inductive TailOk (x : Input) (hs : List GSt) : Nat → List WEv → Prop
  | nil (c : Nat) : TailOk x hs c []
  | ev (c r : Nat) (e : WEv) (rest : List WEv) : c < r → r ≤ hs.length →
      (∀ r', c < r' → r' < r → evAtL x hs r' = none) → evAtL x hs r = some e →
      TailOk x hs r rest → TailOk x hs c (e :: rest)
  | bm (c p : Nat) (o : Obj) (rest : List WEv) : c ≤ p → p ≤ hs.length →
      uint.nat o.ResourceVersion' = p → o.Annotated' = false →
      (∀ r', c < r' → r' ≤ p → evAtL x hs r' = none) →
      TailOk x hs p rest → TailOk x hs c (⟨3, o⟩ :: rest)

/-- The events that are not errors. -/
def nonErr (evs : List WEv) : List WEv := evs.filter fun e => e.t ≠ 4

/-- What a watch of `x`, requested from the revision `req`, delivered (see the file header). -/
def StreamOkL (x : Input) (req : Nat) (hs : List GSt) (evs : List WEv) : Prop :=
  (∀ e ∈ evs, e.t ≤ 4) ∧
  if x.SendInit' = W64 2 then
    ∃ r0, max req 1 ≤ r0 ∧ r0 ≤ hs.length ∧
      (nonErr evs <+: initialEventsL x (histN hs r0) ∨
        ∃ (o : Obj) (tail : List WEv), uint.nat o.ResourceVersion' = r0 ∧ o.Annotated' = true ∧
          nonErr evs = initialEventsL x (histN hs r0) ++ ⟨3, o⟩ :: tail ∧ TailOk x hs r0 tail)
  else ∃ s0, (0 < req → s0 = req) ∧ TailOk x hs s0 (nonErr evs)

/-- The requests the driver makes (`genWatch`): a watch-list asks for NotOlderThan; RV 0 without
a watch-list asks for `SendInitialEvents = false` and NotOlderThan; any other RV the legacy match. -/
def WatchInOk (x : Input) (req : Nat) : Prop :=
  (x.SendInit' = W64 2 → x.Match' = W64 1) ∧
  (x.SendInit' ≠ W64 2 → (req = 0 ∧ x.Match' = W64 1) ∨ (0 < req ∧ x.Match' = W64 0))

/-- What the model's histories satisfy, for the watch check: the stores' items carry
revisions from 1 to the store's own, and no annotation; a change's new object carries the change's
revision; fewer than `2^63` revisions (see the file header). -/
def HistWf (x : Input) (hs : List GSt) : Prop :=
  hs.length < 2 ^ 63 ∧
  (∀ r it, r ≤ hs.length → it ∈ (histN hs r).items →
    1 ≤ uint.nat it.obj'.ResourceVersion' ∧ uint.nat it.obj'.ResourceVersion' ≤ r ∧
    it.obj'.Annotated' = false) ∧
  (∀ r e, evAtL x hs r = some e → uint.nat e.o.ResourceVersion' = r ∧ e.o.Annotated' = false)

/-- An event `encodeWEvents` encodes faithfully: its type is a byte, its object's fields fit, and
its object's encoding is shorter than `2^63`. -/
def WEvOk (e : WEv) : Prop := e.t < 256 ∧ fitsD e.o ∧ (encodeWith tagV1 e.o).length < 2 ^ 63

end go

end k8s_etcd3
end EtcdGrove
end Perennial

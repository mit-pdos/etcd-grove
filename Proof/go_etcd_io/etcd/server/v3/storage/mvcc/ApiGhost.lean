/-
**The API proof's ghost state for a watch stream's filters** (stage 1, 2026-11-03;
`notes/mvcc-api-invariants.md` §1). Lean-first (no Rocq counterpart).

A watcher's filter predicates (`WInfo.fs : List (EvM → Bool)`, `ApiState.lean`) are functions, and
Perennial's ghost values are of small countable types only (`Perennial/Ghost/All.lean`'s codes;
`ghostVar` needs `Pos.Countable`). Saved propositions can hold them, but their agreement holds only
under a later, which `wsRecv_ok.law`'s plain entailment cannot strip. So the filters are saved as a
*discrete* function: `fsCode fs : Pos → DiscreteO (Option Bool)` (code `discreteFunO pos (leibnizO
(option bool))`), the `i`-th filter's verdict on an event at the code of `(i, ev)`, `none` past the
list. Its agreement is pure equality, with no later (`savedFilters_agree`), and `fsCode` is injective
(`fsCode_inj`). A registry element (`ι.reg`) names its watcher's saved filters by a ghost name,
which is countable.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.ApiState
public import Perennial.Ghost.SavedProp

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc
namespace api

open Iris Iris.BI OFE

/-- **The code of a watcher's filters**: at the code of `(i, ev)`, the `i`-th filter's verdict on
`ev` (`none` past the list); elsewhere `none`. -/
def fsCode (fs : List (EvM → Bool)) : Pos → DiscreteO (Option Bool) := fun p =>
  ⟨match (Pos.Countable.decode p : Option (Nat × EvM)) with
   | some (i, ev) => fs[i]?.map (fun f => f ev)
   | none => none⟩

theorem fsCode_at (fs : List (EvM → Bool)) (i : Nat) (ev : EvM) :
    (fsCode fs (Pos.Countable.encode (i, ev))).car = fs[i]?.map (fun f => f ev) := by
  simp [fsCode, Pos.Countable.decode_encode]

/-- A stand-in event (the code needs one to tell a filter from none). -/
def evDummy : EvM := ⟨false, ⟨[], W64 0, W64 0, W64 0, [], W64 0⟩, none⟩

/-- **The code determines the filters.** -/
theorem fsCode_inj {fs fs' : List (EvM → Bool)} (h : fsCode fs = fsCode fs') : fs = fs' := by
  have hat : ∀ (i : Nat) (ev : EvM), fs[i]?.map (fun f => f ev) = fs'[i]?.map (fun f => f ev) := by
    intro i ev
    rw [← fsCode_at, ← fsCode_at, h]
  apply List.ext_getElem?
  intro i
  cases h1 : fs[i]? with
  | none =>
    cases h2 : fs'[i]? with
    | none => rfl
    | some g => have := hat i evDummy; rw [h1, h2] at this; simp at this
  | some f =>
    cases h2 : fs'[i]? with
    | none => have := hat i evDummy; rw [h1, h2] at this; simp at this
    | some g =>
      congr 1
      funext ev
      have := hat i ev
      rw [h1, h2] at this
      simpa using this

section ghost
variable {GF : BundledGFunctors} [AllG GF]

/-- **A watcher's saved filters** (persistent): the ghost name `γ` holds `fs`'s code. -/
def savedFilters (γ : GName) (fs : List (EvM → Bool)) : IProp GF :=
  savedAnythingOwn (T := Pos → DiscreteO (Option Bool)) γ .discard (fsCode fs)

instance savedFilters_persistent (γ : GName) (fs : List (EvM → Bool)) :
    Persistent (savedFilters (GF := GF) γ fs) := by
  unfold savedFilters; infer_instance

/-- A watcher's filters saved under a fresh name. -/
theorem savedFilters_alloc (fs : List (EvM → Bool)) :
    ⊢ |==> ∃ γ, savedFilters (GF := GF) γ fs :=
  saved_anything_alloc (fsCode fs) .discard DFrac.valid_discard

/-- **Saved filters agree**, with no later. -/
theorem savedFilters_agree (γ : GName) (fs fs' : List (EvM → Bool)) :
    savedFilters (GF := GF) γ fs ∗ savedFilters γ fs' ⊢ ⌜fs = fs'⌝ := by
  refine (saved_anything_valid_2 γ .discard .discard (fsCode fs) (fsCode fs')).trans ?_
  refine and_elim_r.trans ?_
  refine (discreteFun_equivI_mp (fsCode fs) (fsCode fs')).trans ?_
  have : (iprop(∀ p, fsCode fs p ≡ fsCode fs' p) : IProp GF) ⊢ ⌜∀ p, fsCode fs p = fsCode fs' p⌝ :=
    (forall_mono fun p => discrete_eq_mp).trans pure_forall.mpr
  refine this.trans (pure_mono fun h => fsCode_inj (funext h))

end ghost

end api
end mvcc
end EtcdGrove
end Perennial

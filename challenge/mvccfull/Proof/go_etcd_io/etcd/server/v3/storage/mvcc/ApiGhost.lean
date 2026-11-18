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

section ghost
variable {GF : BundledGFunctors} [AllG GF]

/-- **A watcher's saved filters** (persistent): the ghost name `γ` holds `fs`'s code. -/
def savedFilters (γ : GName) (fs : List (EvM → Bool)) : IProp GF :=
  savedAnythingOwn (T := Pos → DiscreteO (Option Bool)) γ .discard (fsCode fs)

end ghost

end api
end mvcc
end EtcdGrove
end Perennial

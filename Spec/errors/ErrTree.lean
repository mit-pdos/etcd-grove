/-
**Error trees for `errors.Is`** (2026-11-22, wal-safe session 11; ledger 2026-11-22, "`fmt.ErrorfErrsNot.spec`/
`fmt.ErrorfErrsTerm.spec` -- premises no proof can use"): what a wrapper's `errors.Is` needs of the error it wraps.

Go's `errors.Is(err, target)` walks `err`'s tree itself (`is`, a loop over `Unwrap`): it never calls `errors.Is` on
a wrapped error, so a triple of `errors.Is(child, _)` (`errIsNot`, `errIsTerm`) says nothing a proof of the wrapper's
`errors.Is` can use. These predicates state instead the tree Perennial's `errors.Is.spec` takes
(`errorIsTree S M target`: for each error of `S`, its `Is` method's `true` only if `M`, its `Unwrap` into `S`):

- `errTreeNot e t`: `e` is not `t`, and `e` is in such a tree at the target `t` in which no error is `t` and no `Is`
  method answers `true` (`M` false on `S`): `errors.Is(e, t)` answers `false` (`errIsNot_of_tree`);
- `errTreeTerm e`: for every pointer target `u`, `e` is in such a tree at `u`: `errors.Is(e, u)` returns
  (`errIsTerm_of_tree`).

Both compose: a `*fmt.wrapError` of an error with a tree has one (`Proof/errors/ErrTree.lean`). Lean-first.
-/
module

public import Perennial.Proof.errors.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **`e` is not `t`, and is in an error tree at `t` that has no `t` and no `Is` answering `true`**
(persistent; see the file header). -/
def errTreeNot (e t : GoInterface) : IProp GF :=
  iprop(⌜e ≠ t⌝ ∗ ∃ (S : GoError → Prop) (M : GoInterfaceOk → Prop),
    _root_.Perennial.errors.errorIsTree (GF := GF) S M t ∗
    ⌜S e ∧ _root_.Perennial.errors.TreeTyped S t ∧
      ∀ ii, S (interface.ok ii) → interface.ok ii ≠ t ∧ ¬ M ii⌝)

instance errTreeNot_persistent (e t : GoInterface) : Persistent (errTreeNot (GF := GF) e t) := by
  unfold errTreeNot; infer_instance

/-- **`e` is in an error tree at every pointer target** (persistent; see the file header). -/
def errTreeTerm (e : GoInterface) : IProp GF :=
  iprop(□ ∀ u : GoInterface, ⌜∀ tii, u = interface.ok tii → _root_.Perennial.errors.IsPointerError tii⌝ →
    ∃ (S : GoError → Prop) (M : GoInterfaceOk → Prop),
      _root_.Perennial.errors.errorIsTree (GF := GF) S M u ∗ ⌜S e ∧ _root_.Perennial.errors.TreeTyped S u⌝)

instance errTreeTerm_persistent (e : GoInterface) : Persistent (errTreeTerm (GF := GF) e) := by
  unfold errTreeTerm; infer_instance

end defs

end EtcdGrove
end Perennial

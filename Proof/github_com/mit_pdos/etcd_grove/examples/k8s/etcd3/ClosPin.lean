/- Lean-first (no Rocq counterpart).

**A closure's captured cells** (k8s 7g, `realCheck`). A Go closure is a `GoFunc` value whose body holds
the locations of the variables it captures (Goose allocates each captured variable). Two closure values
that are equal hold the same locations, so a read-only points-to of each pins what they captured: this
is how `realCheck`'s porcupine model tells that two operations with the same `Request` value (the same
`validateFor`/`tryUpdateFor` closure) have the same callback, and so step alike.

- `exprVals e`: the values at the leaves of `e`, in order (through the expression constructors a closure's
  body uses; a location is a value `#l`, whose encoding Perennial keeps abstract, injective only).
- `validatePin has reject vf`: `vf`'s values 14 and 20 (where `validateFor`'s body reads its captured
  `rejects` and `reject`) are read-only cells holding them.
- `tryUpdatePin inp uf`: `uf`'s value 65 (where `tryUpdateFor`'s body reads its captured `in`) is a
  read-only cell holding it.

The indices are those of the translated bodies (`Code/.../k8s/etcd3.lean`); the specs' proofs check them.
A general fact about Perennial's `Expr` (candidate for Perennial: notes/perennial-changes.md,
2026-11-19 "closure values and their captured cells").
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Callbacks

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Input Obj)

section pure
variable [GooseExts]

/-- **The values at the leaves of an expression**, in order (see the file header). -/
def exprVals : Expr → List val
  | .Val v => [v]
  | .Rec _ _ e => exprVals e
  | .App a b => exprVals a ++ exprVals b
  | .If a b c => exprVals a ++ exprVals b ++ exprVals c
  | .Pair a b => exprVals a ++ exprVals b
  | .Fst a => exprVals a
  | .Snd a => exprVals a
  | .Primitive1 _ a => exprVals a
  | .Primitive2 _ a b => exprVals a ++ exprVals b
  | .Catch a b c => exprVals a ++ exprVals b ++ exprVals c
  | _ => []

end pure

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **`validateFor(rejects, reject)`'s closure `vf` captured `rejects` and `reject`** (persistent). -/
def validatePin (has : Bool) (reject : GoString) (vf : GoFunc) : IProp GF :=
  iprop(∃ lh lr : Loc, ⌜(exprVals vf.e)[14]? = some #lh ∧ (exprVals vf.e)[20]? = some #lr⌝ ∗ lh ↦□ has ∗ lr ↦□ reject)

instance validatePin_persistent (has : Bool) (reject : GoString) (vf : GoFunc) :
    Persistent (validatePin (GF := GF) has reject vf) := by
  unfold validatePin; infer_instance

/-- **`tryUpdateFor(in)`'s closure `uf` captured `in`** (persistent). -/
def tryUpdatePin (inp : Input) (uf : GoFunc) : IProp GF :=
  iprop(∃ l : Loc, ⌜(exprVals uf.e)[65]? = some #l⌝ ∗ l ↦□ inp)

instance tryUpdatePin_persistent (inp : Input) (uf : GoFunc) :
    Persistent (tryUpdatePin (GF := GF) inp uf) := by
  unfold tryUpdatePin; infer_instance

/-- **One closure captured one `rejects` and one `reject`.** -/
theorem validatePin_agree (h1 h2 : Bool) (r1 r2 : GoString) (vf : GoFunc) :
    (validatePin h1 r1 vf ∗ validatePin h2 r2 vf : IProp GF) ⊢ ⌜h1 = h2 ∧ r1 = r2⌝ := by
  iintro ⟨H1, H2⟩
  iunfold validatePin at H1 H2
  icases H1 with ⟨%a1, %b1, %e1, #Ha1, #Hb1⟩
  icases H2 with ⟨%a2, %b2, %e2, #Ha2, #Hb2⟩
  obtain rfl : a1 = a2 := go.intoVal_inj (Option.some.inj (e1.1.symm.trans e2.1))
  obtain rfl : b1 = b2 := go.intoVal_inj (Option.some.inj (e1.2.symm.trans e2.2))
  icombine Ha1 Ha2 gives %ha
  icombine Hb1 Hb2 gives %hb
  ipureintro; exact ⟨ha, hb⟩

/-- **One closure captured one `in`.** -/
theorem tryUpdatePin_agree (x1 x2 : Input) (uf : GoFunc) :
    (tryUpdatePin x1 uf ∗ tryUpdatePin x2 uf : IProp GF) ⊢ ⌜x1 = x2⌝ := by
  iintro ⟨H1, H2⟩
  iunfold tryUpdatePin at H1 H2
  icases H1 with ⟨%a1, %e1, #Ha1⟩
  icases H2 with ⟨%a2, %e2, #Ha2⟩
  obtain rfl : a1 = a2 := go.intoVal_inj (Option.some.inj (e1.symm.trans e2))
  icombine Ha1 Ha2 gives %h
  ipureintro; exact h

end defs

end k8s_etcd3
end EtcdGrove
end Perennial

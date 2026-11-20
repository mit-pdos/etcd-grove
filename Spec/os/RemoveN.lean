/-
`os.Remove(name)` of a file whose name is in a claim on any set of names `N` (`N.Mem b`), not only
`.only [b]` (`Spec/os/Remove.lean`'s `specFileSnc`, generalized): the caller holds a fraction of the
claim `(j, N, h)`, the atomic update the rest. What a remover needs when the name is in a directory's
claim on all its names but a few: a WAL purger removing a segment under the WAL directory's claim
(`(j, .except X, hj)`, half the handle's, half the WAL invariant's; unit `locks`, session 6,
`notes/wal-units/locks.md`). The outcome: the unlink logged at `x` by a call begun at `s`, the claim's
names after it being `N`'s restriction of the directory with `b` gone (`rmFileOutN`).

Proved in `Proof/os/RemoveN.lean` (the proof of `specFileSnc` with the claim generalized, over
`Proof/os/UnlinkN.lean`). Lean-first (no Rocq counterpart).
-/
module

public import Spec.os.Remove

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI
open Fs

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [os.Assumptions]

/-- The claim `(j, N, h)` after an unlink's outcome of the file `i` at `b`, with fraction `dq`. -/
def rmFileOutN (j : Ino) (N : NameSet) (b : GoString) (i : Ino) (h : NamesH) (dq : DFrac)
    (o : Option (Nat × Nat)) : IProp GF :=
  iprop(logOut h.next (rmFileEnt j b i) o ∗
    claimOut j N dq h (rmFileEnt j b i) (restrictN N (GMap.delete b h.cur)) o)

/-- See the file header. -/
abbrev os.Remove.specFileSncN : Prop :=
  ∀ (d b : GoString) (j i : Ino) (N : NameSet) (R : Roots) (dq : DFrac) (h : NamesH) (q r qc : Qp)
    (Q : Option (Nat × Nat) → IProp GF),
  NameOk b → N.Mem b → h.cur !! b = some (.file i) → q + r = 1 →
  {{ osInv (GF := GF) ∗ osSharedInv R ∗ osPathS R d dq j ∗ osCallPerm (callKey R d) qc ∗
      osNames j N (DFrac.own q) h ∗
      osAUnc (osNames j N (DFrac.own r) h) (rmFileOutN j N b i h (DFrac.own r)) Q }}
    (App (Val (@! os.Remove)) (Val #(child d b)))
  {{ (err : GoInterface), RET #err; osPathS R d dq j ∗ osCallPerm (callKey R d) qc ∗
      ∃ o, ⌜err = interface.nil → o.isSome⌝ ∗ Q o ∗ rmFileOutN j N b i h (DFrac.own q) o }}

end spec

end EtcdGrove
end Perennial

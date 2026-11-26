/-
The vocabulary of zerolog's per-function axioms (dsv-fix4, mit-pdos/etcd-grove#49 fix 4): the event
token, fixed. Until dsv-fix4 rabia's statement premise `zerolog.Hyps` said only that **some**
predicate makes the event specs true (`∃ ownEvent, EventSpecs ownEvent`, `Spec.lean`); the axioms
(`Logger__*.lean`, `Event__*.lean`) are stated over this one.

`eventTok e`: real zerolog's "`e` is `nil`, or a pooled `*Event` of one of the five levels `Trace`,
`Debug`, `Info`, `Warn`, `Error` that its holder alone uses" (an event is not safe for concurrent
use: its methods append to its buffer). Defined (dsv-retire-3 session 6, 2026-11-26; until then
opaque): `e` is `null` (a disabled level), or `e` points to an `Event` the holder owns, with its
buffer owned and non-empty (`newEvent` starts it with `{`; `AppendKey` reads its last byte), its
writer the one `New(nil)` gives (`newLevelWriter` of `ioutil.Discard`'s value), no `done`, no
hooks, no stack, and a level among the five (`fiveLevels`). Exactly what `Logger.newEvent` of a
`New(nil)` logger leaves (`Logger__*.lean`), and what `Str` keeps (`Event__Str.lean`).
-/
module

public import Dsverify.Proof.github_com.rs.zerolog.Spec

@[expose] public section

noncomputable section

namespace Perennial.github_com.rs.zerolog

open Iris Iris.BI

section def_
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [sem : go.Semantics]

/-- The event token (the file header). -/
def eventTok (e : Loc) : IProp GF :=
  iprop(⌜e = null⌝ ∨ ∃ (v : Event) (bs : List w8) (w : GoInterface),
    e ↦ v ∗ v.buf' ↦* bs ∗ ownSliceCap w8 v.buf' (DFrac.own 1) ∗ ⌜bs ≠ []⌝ ∗
    globalAddr _root_.Perennial.io.ioutil.Discard ↦□ w ∗
    ⌜v.w' = newLevelWriter w ∧ v.done' = func.nil ∧ v.ch' = slice.nil ∧ v.stack' = false ∧
      v.level' ∈ fiveLevels⌝)

end def_

end Perennial.github_com.rs.zerolog

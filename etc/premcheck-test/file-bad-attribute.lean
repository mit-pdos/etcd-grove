/-
**The libraries' premises: yours.** The challenge's statement (`{{SPEC_FILE}}`) takes one premise,
`(∀ G L, letI := heapAt G L; KitLibs remoteGF) →`: this class, at every machine's heap. Put here
what the system's libraries do that the proof needs and the challenge does not prove: each field one
of
- a Hoare triple (or a `∀`/`→`/`∧`/`∃` of triples, or a definition or structure of them) about a
  function or method of a **library** package: not the system's packages ({{SYSTEM}}), not the
  driver's, not `net` (its specs are proved);
- a library package's `InitHyp` (`Dsverify/Proof/<pkg>/Init.lean`: its initializer runs);
- library data (types and predicates, e.g. an exclusive token `Loc → IProp GF`).
Never the system's code or globals (but a precondition may take a system global's points-to), the
kit's protocol or ghost state, or the conclusion. Each premise must be true of the real library: its
precondition what the Go code needs (`TRUST.md`). `etc/premcheck.py etc/dsv/{{KIT}}-premcheck.conf`
checks the rules.

This file may hold only `def`/`abbrev`/`structure`/`class` declarations (and `namespace`, `section`,
`open`, `variable`, `set_option linter.*`); it may import only the challenge's own modules (not
your other files): the lab builds the statement with this file as you leave it. A non-vacuity
instance, `theorem kitLibs_nonvacuity : kitLibs.premise` in `{{INSTANCE_FILE}}`, must build: from
proved specs where you have them, else from axioms in that file alone, each about one library
function (the lab judges whether each is true of Go).
-/
module

public import Dsverify.Proof.rabia.examples.rabianet.TopLevelDefs

@[expose] public section

noncomputable section

set_option linter.iris.style.nameCheck false

namespace Perennial

open Iris Iris.BI Net

namespace rabia.examples.rabianet

/-- The libraries' premises (the file header). -/
class KitLibs [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt] [GoGlobalContext]
    (GF : BundledGFunctors) [HeapGS HasLC.hasLC GF] [go.Semantics] : Prop where

attribute [instance] Nat.instDecidableEq
end rabia.examples.rabianet
end Perennial

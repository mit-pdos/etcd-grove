/-
Lean-first (no Rocq counterpart).

# Porcupine PR #46: package initialization (2026-11-02)

`github.com/anishathalye/porcupine` at PR #46 (`third_party/porcupine-dag`) has package-level
variables the checker reads: the public entry points pass `Linearizability`, a `Consistency`
whose oracles slice holds `RealTime` and `GeneralLikely` and whose validity is `RVal`. Its
package fact (`linInit`) is that `Linearizability` holds such a value, read-only
(`isLinearizability`); the closures are the translation's func literals (`Closures.lean`,
generated), whose specs are lemmas (`Oracles.lean`). A Go client that assigns
`porcupine.Linearizability`, or `LinearizabilityOracles[k]` (which shares its array), is outside
the specs; assigning `RealTime`, `GeneralLikely` or `RVal` does not matter (copied at
initialization). The packages it imports have their facts (Perennial's `context`, `errors`,
`fmt`, `sort`, `strings`, `time`).
-/
module

public import PorcupineDag.GeneratedProof.github_com.anishathalye.porcupine
public import PorcupineDag.Proof.github_com.anishathalye.porcupine.Closures
public import PorcupineDag.Proof.github_com.anishathalye.porcupine.Chains
public import Perennial.Proof.context
public import Perennial.Proof.sort
public import Perennial.Proof.time
public import Perennial.Proof.fmt
public import Perennial.Proof.strings
public import Perennial.Proof.errors

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace github_com.anishathalye.porcupine

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.anishathalye.porcupine.Assumptions]

/-- `RVal`'s value: its `Init` and `Step` closures. -/
def rvalV : Validity := { Init' := rvInitV, Step' := rvStepV }

/-- A consistency value that is linearizability: its oracles slice holds `RealTime` and
`GeneralLikely` (read-only), and its validity is `RVal`. -/
def isLinearizability (v : Consistency) : IProp GF :=
  iprop(v.Oracles' ↦*□ [rtV, glV] ∗ ⌜v.Valid' = rvalV⌝)

instance isLinearizability_persistent (v : Consistency) :
    Persistent (isLinearizability (GF := GF) v) := by unfold isLinearizability; infer_instance

/-- The package's fact: `Linearizability` holds linearizability, read-only. -/
def linInit : IProp GF :=
  iprop(∃ v : Consistency, globalAddr Linearizability ↦□ v ∗ isLinearizability v)

instance isPkgInit_inst :
    IsPkgInit (IProp GF) pkg_id.github_com.anishathalye.porcupine :=
  define_is_pkg_init linInit
instance get_isPkgInit_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.github_com.anishathalye.porcupine :=
  build_get_is_pkg_init_wf

end init

end github_com.anishathalye.porcupine

end Perennial

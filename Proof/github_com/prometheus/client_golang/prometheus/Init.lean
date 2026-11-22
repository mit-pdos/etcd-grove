/-
Package initialization of `github_com.prometheus.client_golang.prometheus`
(item 8, 2026-10-17): its facts and trust-boundary axioms; its `wp_initialize'` is in
`InitLinked.lean` (2026-11-19: the proof applies other packages' `wp_initialize'` and
functions' proofs, so it is a linking module, CLAUDE.md "Import tiers").

Its fact (`PkgInit.lean`, `promInit`): the variable `defaultRegistry` holds the default registry, the
model's (`promreg`), naming IDs by `descId`. Its initializer initializes its imports, runs the untranslated
initializers of its other variables (`X.init`, axioms of the translation), which the trust-boundary axiom
`opaqueInitsOk` says run without panicking, and the trusted glue's (`TrustedCode/`, notes/prom-registry.md):
`defaultRegistry.init` initializes the model's package and stores `promreg.NewRegistry()`, and `init.«0»`
runs `SeedBuiltins` (both proved over the model's specs). (Until 2026-11-22 its fact was `True`,
`defaultRegistry.init` among `opaqueInitsOk` and `init.«0»` the trust-boundary axiom `initFuncsOk`.)
-/
module

public import Proof.github_com.prometheus.client_golang.prometheus.PkgInit
public import Perennial.Proof.time.Link
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.promreg.Init

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false
set_option linter.iris.dupNamespace false

noncomputable section

namespace Perennial

/-- `x ∈ [a, ..., x, ...]`, linear in the list (`simp` overflows on the long ones). -/
local macro "mem_tac" : tactic =>
  `(tactic| repeat (first | exact List.Mem.head _ | apply List.Mem.tail))

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section opaqueInits
namespace github_com.prometheus.client_golang.prometheus
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **The trust boundary: `github_com.prometheus.client_golang.prometheus`'s untranslated variable initializers run.**
Goose translates them names-only, so each `X.init` is an axiom of the translation; Go
runs them at program start, and etcd starts, so each returns without panicking.
Satisfiable whatever the semantics (the `X.init`s are uninterpreted constants). -/
axiom opaqueInitsOk :
    ∀ v ∈ ([rmNamesForMemStatsMetrics.init,
        nativeHistogramBounds.init,
        DefBuckets.init,
        errBucketLabelNotAllowed.init,
        errInconsistentCardinality.init,
        separatorByteSlice.init,
        DefaultRegisterer.init,
        DefaultGatherer.init,
        «_».init,
        errQuantileLabelNotAllowed.init,
        CounterMetricTypePtr.init,
        GaugeMetricTypePtr.init,
        UntypedMetricTypePtr.init,
        labelsPool.init,
        V2.init] : List val),
    {{ (True : IProp GF) }} (App (Val v) (Val #())) {{ RET #(); True }}

end github_com.prometheus.client_golang.prometheus
end opaqueInits

end Perennial

/-
Package initialization of `k8s_io.apimachinery.pkg.apis.«meta».v1`
(item 8, 2026-10-17): its facts and trust-boundary axioms; its `wp_initialize'` is in
`InitLinked.lean` (2026-11-19: the proof applies other packages' `wp_initialize'` and
functions' proofs, so it is a linking module, CLAUDE.md "Import tiers").

Its fact is `True`. Its initializer allocates
`schemeBuilder` (no initializer: nil) and `localSchemeBuilder`, initializes its imports, runs
`localSchemeBuilder`'s translated initializer (`&schemeBuilder`), its untranslated `init.0`
(`register.go`: types registered into `scheme` through `reflect`), which the trust-boundary axiom
`initFuncsOk` says returns, and its translated `init.1` (`zz_generated.conversion.go`;
prove-metav1, 2026-11-27, until then `initFuncsOk`), which appends `RegisterConversions` to
`schemeBuilder` (`runtime.SchemeBuilder.Register.wp_proof`). (`ParameterCodec`, until then
`opaqueInitsOk`, is skipped: its goose config.)
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.etcd3.Base
public import Perennial.Proof.time.Link
public import Proof.k8s_io.apimachinery.pkg.runtime.Init
public import Proof.k8s_io.apimachinery.pkg.runtime.schema.Init
public import Proof.k8s_io.apimachinery.pkg.types.Init

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
namespace k8s_io.apimachinery.pkg.apis.«meta».v1
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **The trust boundary: `k8s_io.apimachinery.pkg.apis.«meta».v1`'s untranslated `init` functions return.** Goose
names a package's `func init()`s `init.<k>`, as gc does, and translates them names-only
here, so the model does not unfold them (`@! init.<k>`: the semantics' `functions`, which
the package's `Assumptions` do not constrain for them). Go runs them at program start, and
etcd starts, so each returns without panicking. A fact about the Go code, as the axioms of
other names-only functions (`EtcdGrove.prometheus.MustRegister.wp_proof`). -/
axiom initFuncsOk :
    ∀ f ∈ ([init.«0»] : List GoString),
    {{ (True : IProp GF) }} (App (Val (@! f)) (Val #())) {{ RET #(); True }}

end k8s_io.apimachinery.pkg.apis.«meta».v1
end opaqueInits

end Perennial

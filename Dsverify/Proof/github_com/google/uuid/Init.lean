/-
**Trust-boundary axiom**: `github.com/google/uuid`'s initializer meets Perennial's initialization spec
(`wp_initialize'`: run once, from a table holding its imports' facts, it establishes the package's
fact). `github.com/google/uuid` is translated names (and types) only in the part, its variables' initializers and
`init` functions untranslated, so its `initialize'` cannot be proved here; Go runs them at program
start and they return (the kits' programs start). The axiom states exactly the class `InitHyp`'s
field (the statement, kept for the test-only `InitInstancesLinked.lean`, which derives it from
local axioms on the untranslated initializers); it is per package and in no statement
(mit-pdos/etcd-grove#8, 2026-11-25T02:20:53Z; `etc/dsv/README.md`), counted in the tcb collections
of the kits that initialize the package (swiftpaxos). Review:
`notes/axiom-review/dsv-inits/github-com-google-uuid.md`. To retire: a translation or model of the package with a
proved `wp_initialize'`.
-/
module

public import Dsverify.GeneratedProof.github_com.google.uuid
public import Proof.runtime.PkgInitExt

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace github_com.google.uuid

section def_
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- The package's fact, `True`, written by hand (not `define_is_pkg_init`, which needs the facts of
all its imports, some of which have none in the part): no importer reads the imports' facts
through it. -/
instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.github_com.google.uuid :=
  { isPkgInitDeps := iprop(True), isPkgInitDef := iprop(True) }
/-- Its well-formedness: `get_is_pkg_init` gives its fact (its imports' are not constrained). -/
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.github_com.google.uuid :=
  { get_is_pkg_init_prop_def := fun g => g pkg_id.github_com.google.uuid = isPkgInit pkg_id.github_com.google.uuid ∧ True }

end def_

section init
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [sem : go.Semantics]

/-- The axiom's statement (the file header): `github.com/google/uuid`'s initializer establishes its package fact. -/
class InitHyp [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext] {hlc : HasLC}
    (GF : BundledGFunctors) [HeapGS hlc GF] [go.Semantics] : Prop where
  wp_init : ∀ (get_is_pkg_init : GoString → IProp GF),
    GetIsPkgInitProp pkg_id.github_com.google.uuid get_is_pkg_init →
    {{ ownInitializing get_is_pkg_init }} (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗ isPkgInit (PROP := IProp GF) pkg_id.github_com.google.uuid }}

/-- **Trust-boundary axiom** (the file header): `github.com/google/uuid`'s initialization. -/
axiom wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.github_com.google.uuid get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }} (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗ isPkgInit (PROP := IProp GF) pkg_id.github_com.google.uuid }}

end init

end github_com.google.uuid
end Perennial

/-
**Trust-boundary axiom**: `gopkg.in/yaml.v2`'s initializer meets Perennial's initialization spec
(`wp_initialize'`: run once, from a table holding its imports' facts, it establishes the package's
fact). `gopkg.in/yaml.v2` is translated names (and types) only in the part, its variables' initializers and
`init` functions untranslated, so its `initialize'` cannot be proved here; Go runs them at program
start and they return (the kits' programs start). The axiom states exactly the class `InitHyp`'s
field (the statement, kept for the test-only `InitInstancesLinked.lean`, which derives it from
local axioms on the untranslated initializers); it is per package and in no statement
(mit-pdos/etcd-grove#8, 2026-11-25T02:20:53Z; `etc/dsv/README.md`), counted in the tcb collections
of the kits that initialize the package (quepaxa). Review:
`notes/axiom-review/dsv-inits/gopkg-in-yaml-v2.md`. To retire: a translation or model of the package with a
proved `wp_initialize'`.
-/
module

public import Dsverify.Proof.gopkg_in.yaml_v2.Base
public import Proof.runtime.PkgInitExt

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic

namespace gopkg_in.yaml_v2

/-- The axiom's statement (the file header): `gopkg.in/yaml.v2`'s initializer establishes its package fact. -/
class InitHyp [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext] {hlc : HasLC}
    (GF : BundledGFunctors) [HeapGS hlc GF] [go.Semantics] : Prop where
  wp_init : ∀ (get_is_pkg_init : GoString → IProp GF),
    GetIsPkgInitProp pkg_id.gopkg_in.yaml_v2 get_is_pkg_init →
    {{ ownInitializing get_is_pkg_init }} (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗ isPkgInit (PROP := IProp GF) pkg_id.gopkg_in.yaml_v2 }}

section init
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [sem : go.Semantics]

/-- **Trust-boundary axiom** (the file header): `gopkg.in/yaml.v2`'s initialization. -/
axiom wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.gopkg_in.yaml_v2 get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }} (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗ isPkgInit (PROP := IProp GF) pkg_id.gopkg_in.yaml_v2 }}

end init

end gopkg_in.yaml_v2
end Perennial

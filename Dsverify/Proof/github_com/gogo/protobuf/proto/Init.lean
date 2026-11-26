/-
**Trust-boundary axiom**: `github.com/gogo/protobuf/proto`'s initializer meets Perennial's initialization spec
(`wp_initialize'`: run once, from a table holding its imports' facts, it establishes the package's
fact). `github.com/gogo/protobuf/proto` is translated names (and types) only in the part, its variables' initializers and
`init` functions untranslated, so its `initialize'` cannot be proved here; Go runs them at program
start and they return (the kits' programs start). The axiom states exactly the field of the class `InitHyp`
that was the statement's premise until dsv-fix3 (the class and its test-only derivation
`InitInstancesLinked.lean` deleted with it); it is per package and in no statement
(mit-pdos/etcd-grove#8, 2026-11-25T02:20:53Z; `etc/dsv/README.md`), counted in the tcb collections
of the kits that initialize the package (rabia). Review:
`notes/axiom-review/dsv-inits/github-com-gogo-protobuf-proto.md`. To retire: a translation or model of the package with a
proved `wp_initialize'`.

The axiom asserts only that. The specs of the three `Register*` functions rabia's `message` package
calls in its `init`s, with the preconditions under which they hold, are the separate premise `Hyps`
(`Spec.lean`).
-/
module

public import Dsverify.Proof.github_com.gogo.protobuf.proto.Base
public import Proof.runtime.PkgInitExt

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic

namespace github_com.gogo.protobuf.proto

section init
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [sem : go.Semantics]

/-- **Trust-boundary axiom** (the file header): `github.com/gogo/protobuf/proto`'s initialization. -/
axiom wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.github_com.gogo.protobuf.proto get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }} (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗ isPkgInit (PROP := IProp GF) pkg_id.github_com.gogo.protobuf.proto }}

end init

end github_com.gogo.protobuf.proto
end Perennial

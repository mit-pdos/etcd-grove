/-
**Trust-boundary axiom**: `os/signal`'s initializer meets Perennial's initialization spec
(`wp_initialize'`: run once, from a table holding its imports' facts, it establishes the package's
fact). `os/signal` is translated names (and types) only in the part, its variables' initializers and
`init` functions untranslated, so its `initialize'` cannot be proved here; Go runs them at program
start and they return (the kits' programs start). The axiom states exactly the field of the class `InitHyp`
that was the statement's premise until dsv-fix3 (the class and its test-only derivation
`InitInstancesLinked.lean` deleted with it); it is per package and in no statement
(mit-pdos/etcd-grove#8, 2026-11-25T02:20:53Z; `etc/dsv/README.md`), counted in the tcb collections
of the kits that initialize the package (swiftpaxos, rabia). Review:
`notes/axiom-review/dsv-inits/os-signal.md`. To retire: a translation or model of the package with a
proved `wp_initialize'`.
-/
module

public import Dsverify.Proof.os.signal.Base
public import Proof.runtime.PkgInitExt

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic

namespace os.signal

section init
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [sem : go.Semantics]

/-- **Trust-boundary axiom** (the file header): `os/signal`'s initialization. -/
axiom wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.os.signal get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }} (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗ isPkgInit (PROP := IProp GF) pkg_id.os.signal }}

end init

end os.signal
end Perennial

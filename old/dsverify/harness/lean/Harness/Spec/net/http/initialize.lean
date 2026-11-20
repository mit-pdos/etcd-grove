/-
`net/http`'s package initializer (`net.http.initialize'`, generated in `Code/net/http.lean`):
it allocates `errHead`, `DefaultServeMux` and `errStatus`, initializes `sync`, `net`, `errors` and
`bufio`, then sets `errStatus = errors.New(...)`, `DefaultServeMux = NewServeMux()` and
`errHead = errors.New(...)`. The spec: from
`ownInitializing`, it returns with `isPkgInit pkg_id.net.http` (`net.http.isInit`). Proved in
`Proof/net/http/initialize.lean`.
-/
module

public import Harness.Proof.net.http.Base
public import Perennial.Spec.sync.initialize
public import Perennial.Spec.errors.initialize
public import Harness.Spec.net.initialize
public import Harness.Proof.bufio.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [net.http.Assumptions]

/-- See the file header. -/
abbrev net.http.initialize'.spec : Prop :=
  ∀ (get_is_pkg_init : GoString → IProp GF),
  GetIsPkgInitProp pkg_id.net.http get_is_pkg_init →
    {{ ownInitializing get_is_pkg_init }}
      (App (Val net.http.initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.net.http }}

end spec

end Perennial

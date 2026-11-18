/-
`net/rpc`'s package initializer (`net.rpc.initialize'`, generated in `Code/net/rpc.lean`):
it allocates its globals, initializes `net/http`, `sync`, `net` and `errors`, then sets
`ErrShutdown`, `errHTTP`, `DefaultServer = NewServer()` and `errFrame`. The spec: from
`ownInitializing`, it returns with `isPkgInit pkg_id.net.rpc` (`net.rpc.isInit`). Proved in
`Proof/net/rpc/initialize.lean`.
-/
module

public import Harness.Proof.net.rpc.Base
public import Harness.Spec.net.http.initialize
public import Perennial.Spec.sync.initialize
public import Perennial.Spec.errors.initialize
public import Harness.Spec.net.initialize

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [net.rpc.Assumptions] [net.rpc.RpcKit]

/-- See the file header. -/
abbrev net.rpc.initialize'.spec : Prop :=
  ∀ (get_is_pkg_init : GoString → IProp GF),
  GetIsPkgInitProp pkg_id.net.rpc get_is_pkg_init →
    {{ ownInitializing get_is_pkg_init }}
      (App (Val net.rpc.initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.net.rpc }}

end spec

end Perennial

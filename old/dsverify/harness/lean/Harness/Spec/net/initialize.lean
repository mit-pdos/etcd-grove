/-
`net`'s package initializer (`net.initialize'`, generated in `Code/net.lean`): it initializes
`time` and `io` (the packages the translated `net` imports) and runs each package variable's
trusted initializer (`TrustedCode/net.lean`): all do nothing but `ErrClosed.init`, which
allocates the model's `poll.ErrNetClosing` (`net#model.errNetClosing`) and `net.ErrClosed`, both
holding one `&connError{false, false}`. The spec: from `ownInitializing`, it returns with
`isPkgInit pkg_id.net` (`net.isInit`, with `time`'s and `io`'s). Proved in
`Proof/net/initialize.lean` from the specs of `time.initialize'` and `io.initialize'`.
-/
module

public import Harness.Proof.net.Base
public import Perennial.Spec.time.initialize
public import Perennial.Spec.io.initialize

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [net.Assumptions] [net.model.Assumptions]

/-- See the file header. -/
abbrev net.initialize'.spec : Prop :=
  ∀ (get_is_pkg_init : GoString → IProp GF),
  GetIsPkgInitProp pkg_id.net get_is_pkg_init →
    {{ ownInitializing get_is_pkg_init }}
      (App (Val net.initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.net }}

end spec

end Perennial

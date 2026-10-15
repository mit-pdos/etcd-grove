/-
`context.WithTimeout(context.Background(), d)`: the trust boundary (Perennial specifies
`WithTimeout` of an `isContext` parent only, and `Background()` is none: its `Done()` is `nil`).
Lean-first (no Rocq counterpart); the request path's unit 4a (the read loop's `sendReadIndex`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.BaseApply
public import Perennial.Proof.context

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI 

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : context.Assumptions]

/-- `context.WithTimeout(context.Background(), d)` (`context.closedchan` closed, the package's
ghost fact `isClosedchanInit`): a context (`isContext`, of some descriptor: a `*timerCtx` whose
parent is `Background()`) and its `cancel` function, callable from anywhere. What Perennial's
`context.WithDeadlineCause` proof shows of an `isContext` parent (`isContext_timerCtx`,
`wp_propagateCancel_background`), for the parent `Background()`, which Perennial's proof does not
take; Go's `WithTimeout(parent, d)` is `WithDeadline(parent, time.Now().Add(d))`. -/
abbrev context.WithTimeoutBackground.spec : Prop :=
  ∀ (d : _root_.Perennial.time.Duration),
  {{ isPkgInit (PROP := IProp GF) pkg_id.context ∗ context.isClosedchanInit }}
    (App (App (Val (@! _root_.Perennial.context.WithTimeout))
      (Val #(interface.ok context.backgroundCtxVal))) (Val #d))
  {{ (ctx' : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (cancel : GoFunc),
      RET (PairV #(interface.ok ctx') #cancel);
      □ (∀ Φ : val → IProp GF, True -∗ ▷ (True -∗ Φ #()) -∗
        WP (App (Val #cancel) (Val #())) {{ Φ }}) ∗
      context.isContext ctx' cd }}

end spec

end EtcdGrove
end Perennial

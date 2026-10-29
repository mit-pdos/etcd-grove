/-
`context.WithTimeout(context.Background(), d)`, in the form the read loop's `sendReadIndex` (the
request path's unit 4a) and the examples' call sites (`client.wp_WithTimeout_bg`) use: a context
of some descriptor and its `cancel`. Proved from Perennial's `wp_WithTimeout_Background` since the
pin of 2026-10-23 (`notes/client-timeouts-plan.md` T3); the trust boundary until then, Perennial
specifying `WithTimeout` of an `isContext` parent only. Lean-first (no Rocq counterpart).
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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : context.Assumptions]

/-- `context.WithTimeout(context.Background(), d)` (`context.closedchan` closed, the package's
ghost fact `isClosedchanInit`, a premise its proof no longer needs): a context (`isContext`, of
some descriptor: a `*timerCtx` whose parent is `Background()`) and its `cancel` function, callable
from anywhere. Perennial's `wp_WithTimeout_Background` says which descriptor (no values, the
deadline `time.Now().Add(d)`, Done proposition `True`); the callers here need only that it has no
values (authkv's `reqCtx`: so no outgoing metadata, `metadata.outgoingOf_noValues`). -/
abbrev context.WithTimeoutBackground.spec : Prop :=
  ∀ (d : _root_.Perennial.time.Duration),
  {{ isPkgInit (PROP := IProp GF) pkg_id.context ∗ context.isClosedchanInit }}
    (App (App (Val (@! _root_.Perennial.context.WithTimeout))
      (Val #(interface.ok context.backgroundCtxVal))) (Val #d))
  {{ (ctx' : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (cancel : GoFunc),
      RET (PairV #(interface.ok ctx') #cancel);
      □ (∀ Φ : val → IProp GF, True -∗ ▷ (True -∗ Φ #()) -∗
        WP (App (Val #cancel) (Val #())) {{ Φ }}) ∗
      context.isContext ctx' cd ∗ ⌜cd.Values = ∅⌝ }}

end spec

end EtcdGrove
end Perennial

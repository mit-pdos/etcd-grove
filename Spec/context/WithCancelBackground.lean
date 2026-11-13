/-
`context.WithCancel(context.Background())` (rafthttp's `pipeline.post`; stage 4d). Perennial's
`wp_WithCancel` takes an `isContext` parent, which `Background()` is not (its `Done()` is `nil`); a
trust-boundary axiom until k8s 7f-4's Addendum T-i (2026-11-13), now proved from Perennial's
`wp_WithCancel_gen` (`Proof/context/WithCancelBackground.lean`). Lean-first.
-/
module

public import Perennial.Proof.context
public import Proof.context.BgCancel

@[expose] public section

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

/-- `context.WithCancel(context.Background())`: a cancellable context (`isContext`, no deadline, done
only when cancelled) and its `cancel` function, callable from anywhere. What Go's `WithCancel`
does for a parent that is never done (`propagateCancel` returns at once: `parent.Done()` is
`nil`), as `context.WithCancelValCtx` says of etcd's `valCtx`. (k8s 7f-4, Addendum T-i) A `*cancelCtx`
child of `Background()` (`context.bgCancelChild`): what net/http's round trippers need of a
request's context (`http.reqCtxBg`). -/
abbrev context.WithCancelBackground.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.context }}
    (App (Val (@! _root_.Perennial.context.WithCancel)) (Val #(GoInterface.ok context.backgroundCtxVal)))
  {{ (ctx' : GoInterfaceOk) (γ' : context.ContextNames) (cancel : GoFunc),
      RET (PairV #(interface.ok ctx') #cancel);
      context.cancelSpec cancel γ' iprop(True) ∗
      context.isContext ctx' { Values := ∅, Deadline := none, Done_gn := γ', PDone := iprop(True) } ∗
      context.bgCancelChild ctx' }}

end spec

end EtcdGrove
end Perennial

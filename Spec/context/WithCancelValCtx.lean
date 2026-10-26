/-
`context.WithCancel(&valCtx{inctx})` (`client/v3/watch.go`'s `newWatcherGRPCStream`): the trust
boundary (the watch slice's unit W-C). Perennial specifies `WithCancel` of an `isContext` parent
only, whose `Done()` channel belongs to a `*cancelCtx` chain (`isContext`'s `HParentCC`); etcd's
`valCtx` is none: its `Done()` is the package's never-closed `valCtxCh`, so Go's
`propagateCancel` takes its last branch (a goroutine waiting on the parent's or the child's
`Done()`), which Perennial's model does not cover. Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.Base
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

/-- `context.WithCancel(&valCtx{inctx})` for a context `inctx` (`isContext`; `valCtx`'s fields
read-only): a cancellable context (`isContext`, no deadline: `valCtx.Deadline()` reports none;
done only when cancelled: `valCtx.Done()` is never closed and `valCtx.Err()` is `nil`) and its
`cancel` function, callable from anywhere. What Go's `WithCancel` does for a parent that is
never done (`propagateCancel`'s goroutine waits for the child's `Done()`), as Perennial's
`wp_WithCancel_Background` says of `Background()`; `inctx`'s values are reachable through
`valCtx`'s embedded `Context` (Go's promotion), which the descriptor does not record. -/
abbrev context.WithCancelValCtx.spec : Prop :=
  ∀ (p : Loc) (inctx : GoInterfaceOk) (cs : context.ContextDesc (IProp GF)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.context ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
      p ↦□ (go_etcd_io.etcd.client.v3.valCtx.mk (interface.ok inctx)) ∗
      context.isContext inctx cs }}
    (App (Val (@! _root_.Perennial.context.WithCancel))
      (Val #(interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.valCtx.ty) #p)))
  {{ (ctx' : GoInterfaceOk) (γ' : context.ContextNames) (cancel : GoFunc),
      RET (PairV #(interface.ok ctx') #cancel);
      context.cancelSpec cancel γ' iprop(True) ∗
      context.isContext ctx' { Values := ∅, Deadline := none, Done_gn := γ', PDone := iprop(True) } }}

end spec

end EtcdGrove
end Perennial

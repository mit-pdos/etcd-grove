/-
`context.WithCancel(context.Background())` (rafthttp's `pipeline.post`; stage 4d): the trust
boundary, as `WithCancelTodo`. Perennial specifies `WithCancel` of an `isContext` parent only;
`Background()` is none (its `Done()` is `nil`). Lean-first.
-/
module

public import Perennial.Proof.context
public import Perennial.Proof.context

@[expose] public section

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

/-- `context.WithCancel(context.Background())`: a cancellable context (`isContext`, no deadline, done
only when cancelled) and its `cancel` function, callable from anywhere. What Go's `WithCancel`
does for a parent that is never done (`propagateCancel` returns at once: `parent.Done()` is
`nil`), as `context.WithCancelValCtx` says of etcd's `valCtx`. -/
abbrev context.WithCancelBackground.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.context }}
    (App (Val (@! _root_.Perennial.context.WithCancel)) (Val #(GoInterface.ok context.backgroundCtxVal)))
  {{ (ctx' : GoInterfaceOk) (γ' : context.ContextNames) (cancel : GoFunc),
      RET (PairV #(interface.ok ctx') #cancel);
      context.cancelSpec cancel γ' iprop(True) ∗
      context.isContext ctx' { Values := ∅, Deadline := none, Done_gn := γ', PDone := iprop(True) } }}

end spec

end EtcdGrove
end Perennial

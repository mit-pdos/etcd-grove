/-
`context.WithCancel(context.TODO())`: the trust boundary (pr-verify etcd#21714: `clientv3.newClient` of a `Config` with no `Context`). Perennial specifies `WithCancel` of an `isContext` parent, which `TODO()`'s is not. Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.InvEtcdTxn

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

/-- `context.WithCancel(context.TODO())`: a cancellable context (`isContext`, no values, no deadline, done
only when cancelled) and its `cancel` function, callable from anywhere: what Go's `WithCancel` does
for a parent that is never done (`TODO()`'s `Done()` is `nil`: no propagation), as Perennial's
`wp_WithCancel_Background` says of `Background()` (an `emptyCtx` too). -/
abbrev context.WithCancelTODO.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.context }}
    (App (Val (@! _root_.Perennial.context.WithCancel)) (Val #(GoInterface.ok todoCtxVal)))
  {{ (ctx' : GoInterfaceOk) (γ' : context.ContextNames) (cancel : GoFunc),
      RET (PairV #(interface.ok ctx') #cancel);
      context.cancelSpec cancel γ' iprop(True) ∗
      context.isContext ctx' { Values := ∅, Deadline := none, Done_gn := γ', PDone := iprop(True) } }}

end spec

end EtcdGrove
end Perennial

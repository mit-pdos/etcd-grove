/-
`clientv3.WithRequireLeader(context.Background())` (`client/v3/ctx.go`, names only: it needs grpc's
`metadata`; item 1, the client lease: `NewLeaseFromLeaseClient`'s stop context). Lean-first (no
Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvLease
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
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `WithRequireLeader(context.Background())` (`metadata.NewOutgoingContext` of `Background()` with
the `hasleader` metadata): a context `c` that is never done (its `Done()` is `Background()`'s,
`nil`), so that `context.WithCancel(c)` is a cancellable context done only when cancelled
(`propagateCancel` returns at once: `c.Done()` is `nil`), as `context.WithCancelTodo` says of
`TODO()`. -/
abbrev WithRequireLeader.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 }}
    (App (Val (@! go_etcd_io.etcd.client.v3.WithRequireLeader))
      (Val #(GoInterface.ok _root_.Perennial.context.backgroundCtxVal)))
  {{ (c : GoInterfaceOk), RET #(GoInterface.ok c);
      □ iprop({{ isPkgInit (PROP := IProp GF) pkg_id.context }}
        (App (Val (@! _root_.Perennial.context.WithCancel)) (Val #(GoInterface.ok c)))
      {{ (ctx' : GoInterfaceOk) (γ' : context.ContextNames) (cancel : GoFunc),
          RET (PairV #(interface.ok ctx') #cancel);
          context.cancelSpec cancel γ' iprop(True) ∗
          context.isContext ctx'
            { Values := ∅, Deadline := none, Done_gn := γ', PDone := iprop(True) } }}) }}

end spec

end EtcdGrove
end Perennial

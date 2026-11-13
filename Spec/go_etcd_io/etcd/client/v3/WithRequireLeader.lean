/-
`clientv3.WithRequireLeader(ctx)` (`client/v3/ctx.go`, names only: it needs grpc's `metadata`; item 1,
the client lease: `NewLeaseFromLeaseClient`'s stop context over `Background()`; k8s 7f-3a, T5-a: the
etcd3 watcher's context over a caller's). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvLease
public import Perennial.Proof.context
public import Proof.context.LibKeysChain
public import Proof.context.WatchCtx

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
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- **`WithRequireLeader(ctx)`** (`client/v3/ctx.go:28-38`: `metadata.NewOutgoingContext(ctx, md)`, `md`
the caller's outgoing metadata copied, or new, with `hasleader` set; `NewOutgoingContext` is
`context.WithValue(ctx, mdOutgoingKey{}, rawMD{md})`). Restated for k8s 7f-3a (T5-a, decision D1:
the fallback to translating it; `notes/k8s-7f5-freeze.md`, "T5-a addendum"), in `withVersion.spec`'s
pattern, for a parent the client's watch takes (`watchCtx ctx s`) or `Background()`. The result `c`:

* is a context the watch takes, at the parent's descriptor (`watchCtx c s`: its `Done`, `Err` and
  `Value(&cancelCtxKey)` are the parent's, so its `Cause` is too; its outgoing metadata is one grpc
  stored, `metadata.outgoingCtxOkC`);
* answers every key whose type is not grpc's `mdOutgoingKey` as the parent does, in the WP form
  (`c.Value(k)`, from the parent's `ctx.Value(k)` triple) and in the chain form
  (`context.ctxValue`, what a descendant's walk of `context.value` and `WithCancel` carry);
* (the old triple, unchanged, for `Background()`: premise-fixes-7/8, C1) when the parent is
  `Background()`, `WithCancel(c)` is a cancellable context done only when cancelled
  (`propagateCancel` returns at once: `c.Done()` is `nil`), as `context.WithCancelTodo` says of
  `TODO()`, with well-formed library values (`context.libCtxOk ctx'`: grpc's outgoing key answered
  with the `rawMD` `NewOutgoingContext` stored, `builtRawMD`, the other library keys with
  `Background()`'s `nil`) and the same in Perennial's chain (`metadata.outgoingCtxOkC ctx'`: the walk
  goes from the `*cancelCtx` to the `*valueCtx`, never written, whose key is `mdOutgoingKey{}` and
  value that `rawMD`).

The metadata's content (the parent's with `hasleader` set) is not stated (decision D3): no user reads
it (the watch's stream key is generic in it). -/
abbrev WithRequireLeader.spec : Prop :=
  ∀ (ctx : GoInterfaceOk) (s : _root_.Perennial.context.ContextDesc (IProp GF)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
      (EtcdGrove.context.watchCtx ctx s ∨ ⌜ctx = _root_.Perennial.context.backgroundCtxVal⌝) }}
    (App (Val (@! go_etcd_io.etcd.client.v3.WithRequireLeader)) (Val #(GoInterface.ok ctx)))
  {{ (c : GoInterfaceOk), RET #(GoInterface.ok c);
      (EtcdGrove.context.watchCtx ctx s -∗ EtcdGrove.context.watchCtx c s) ∗
      □ (∀ (k : GoInterface) (R : GoInterface → Prop),
          ⌜∀ k' : GoInterfaceOk, k = GoInterface.ok k' →
            k'.ty ≠ google_golang_org.grpc.metadata.mdOutgoingKey.ty⌝ -∗
          {{ True }} (App (Val #(methods ctx.ty go!"Value" ctx.v)) (Val #k))
            {{ (w : GoInterface), RET #w; ⌜R w⌝ }} -∗
          {{ True }} (App (Val #(methods c.ty go!"Value" c.v)) (Val #k))
            {{ (w : GoInterface), RET #w; ⌜R w⌝ }}) ∗
      □ (∀ (k : GoInterface) (R : GoInterface → Prop),
          ⌜∀ k' : GoInterfaceOk, k = GoInterface.ok k' →
            k'.ty ≠ google_golang_org.grpc.metadata.mdOutgoingKey.ty⌝ -∗
          _root_.Perennial.context.ctxValue ctx k R -∗ _root_.Perennial.context.ctxValue c k R) ∗
      (⌜ctx = _root_.Perennial.context.backgroundCtxVal⌝ -∗
        □ iprop({{ isPkgInit (PROP := IProp GF) pkg_id.context }}
          (App (Val (@! _root_.Perennial.context.WithCancel)) (Val #(GoInterface.ok c)))
        {{ (ctx' : GoInterfaceOk) (γ' : context.ContextNames) (cancel : GoFunc),
            RET (PairV #(interface.ok ctx') #cancel);
            context.cancelSpec cancel γ' iprop(True) ∗
            context.isContext ctx'
              { Values := ∅, Deadline := none, Done_gn := γ', PDone := iprop(True) } ∗
            context.libCtxOk ctx' ∗ metadata.outgoingCtxOkC ctx' }})) }}

end spec

end EtcdGrove
end Perennial

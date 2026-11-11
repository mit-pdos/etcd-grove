/-
`metadata.AppendToOutgoingContext` (grpc, `metadata/metadata.go`): the trust boundary (grpc's
`metadata` is types and names only; the auth plan's E2f, contract C3 of `examples/etcd/auth`).
Lean-first (no Rocq counterpart).
-/
module

public import Proof.google_golang_org.grpc.metadata.Outgoing
public import Proof.google_golang_org.grpc.InvGrpc
public import Proof.context.LibKeysChain

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI google_golang_org.grpc

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : context.Assumptions]

/-- `metadata.AppendToOutgoingContext(ctx, k, v)` (one pair, `kv` the slice `[k, v]` read) on a
context with the context model (`isContext`) returns a context derived from `ctx` by a value
(grpc's code: `context.WithValue(ctx, mdOutgoingKey{}, rawMD{md: md, added: added})`, the pair
appended to `added`): the same `Deadline`, `Done` and `Err`, and `Value` at the context package's
own key (a `valueCtx` delegates them to its parent: `isContext` with `ctx`'s descriptor, its values
changed, as `withVersion`'s), and outgoing metadata `ctx`'s with `v` appended to the values of `k`
(a key with no upper-case letter: grpc lower-cases it, and `FromOutgoingContext` and the transport
merge `added` after `md`). Its panic on an odd number of arguments is unreachable (two).
(premise-fixes-7) It reads `ctx.Value(mdOutgoingKey{})` (`metadata.go:254`), so it takes
`metadata.outgoingCtxOk ctx`, and the context it returns has it too: its `Value` at that key is the
new `rawMD` (`builtRawMD`). (premise-fixes-8, C1) So does Perennial's chain
(`metadata.outgoingCtxOkC ci`): `ci` is the `*valueCtx` `WithValue` made (fields never written),
whose key is grpc's `mdOutgoingKey{}` and whose value is that `rawMD`; the chain stops there, so
it holds whatever `ctx` is. -/
abbrev metadata.AppendToOutgoingContext.spec : Prop :=
  ∀ (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (sl : GoSlice) (dq : DFrac)
    (k v : GoString),
  metadata.lowerKey k →
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc.metadata ∗
      context.isContext ctx cd ∗ metadata.outgoingCtxOk ctx ∗ sl ↦*{dq} [k, v] }}
    (App (App (Val (@! google_golang_org.grpc.metadata.AppendToOutgoingContext))
      (Val #(GoInterface.ok ctx))) (Val #sl))
  {{ (c' : GoInterface), RET #c'; ∃ (ci : GoInterfaceOk) (vs : GMap GoInterface GoInterface),
      ⌜c' = GoInterface.ok ci⌝ ∗ context.isContext ci { cd with Values := vs } ∗
      metadata.outgoingCtxOk ci ∗ metadata.outgoingCtxOkC ci ∗
      ⌜metadata.outgoingOf c' = metadata.mdAdd (metadata.outgoingOf (GoInterface.ok ctx)) k v⌝ ∗
      sl ↦*{dq} [k, v] }}

end spec

end EtcdGrove
end Perennial

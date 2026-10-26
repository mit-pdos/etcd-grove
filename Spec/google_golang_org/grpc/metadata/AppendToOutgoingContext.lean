/-
`metadata.AppendToOutgoingContext` (grpc, `metadata/metadata.go`): the trust boundary (grpc's
`metadata` is types and names only; the auth plan's E2f, contract C3 of `examples/authkv`).
Lean-first (no Rocq counterpart).
-/
module

public import Proof.google_golang_org.grpc.metadata.Outgoing
public import Proof.google_golang_org.grpc.InvGrpc

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI google_golang_org.grpc

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
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
merge `added` after `md`). Its panic on an odd number of arguments is unreachable (two). -/
abbrev metadata.AppendToOutgoingContext.spec : Prop :=
  ∀ (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (sl : GoSlice) (dq : DFrac)
    (k v : GoString),
  metadata.lowerKey k →
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc.metadata ∗
      context.isContext ctx cd ∗ sl ↦*{dq} [k, v] }}
    (App (App (Val (@! google_golang_org.grpc.metadata.AppendToOutgoingContext))
      (Val #(GoInterface.ok ctx))) (Val #sl))
  {{ (c' : GoInterface), RET #c'; ∃ (ci : GoInterfaceOk) (vs : GMap GoInterface GoInterface),
      ⌜c' = GoInterface.ok ci⌝ ∗ context.isContext ci { cd with Values := vs } ∗
      ⌜metadata.outgoingOf c' = metadata.mdAdd (metadata.outgoingOf (GoInterface.ok ctx)) k v⌝ ∗
      sl ↦*{dq} [k, v] }}

end spec

end EtcdGrove
end Perennial

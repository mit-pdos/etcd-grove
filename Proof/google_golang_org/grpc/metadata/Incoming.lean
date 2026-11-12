/-
**A context's incoming metadata** (grpc's `metadata`, names-only; the auth plan's E2c,
2026-10-25). Lean-first (no Rocq counterpart).

`metadata.FromIncomingContext(ctx)` copies the metadata a context carries under grpc's
incoming-metadata key (`metadata.NewIncomingContext`, which grpc's transports call with a request's
header fields). A context is immutable: its `Value` for a key is fixed once the context is made, so
the metadata is a function of the context value (`incomingOf`, opaque): `none` when the context has
none, else the values of each key. The auth store's `AuthInfoFromCtx` reads a request's token from
it (`auth.ctxTokenOf`), and the client's side (`metadata.AppendToOutgoingContext`, grpc's delivery
of a call's outgoing metadata as its handler's incoming metadata) is to be stated over it.

(k8s 7f-4, T-b) `incomingOf_of_value` (trusted): it is a function of what `Value(mdIncomingKey{})`
returns, so that a context derived from a handler's (etcd's `cancellableContext` over
`WithCancel(ss.Context())`) has the handler's metadata.
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.Base
public import Proof.context.LibKeys

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace metadata

/-- **The incoming metadata of the context `ctx`** (opaque, see the file header): `none` if it
has none, else each key's values. -/
opaque incomingOf [GooseExts] : GoInterface → Option (GoString → Option (List GoString))

end metadata

section value
open Iris Iris.BI
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- (TRUSTED; k8s 7f-4, T-b) **The incoming metadata is a function of `Value(mdIncomingKey{})`**:
two contexts whose `Value` at grpc's incoming key returns the same value `v` on every call have the
same incoming metadata. `metadata.FromIncomingContext(ctx)` reads only
`ctx.Value(mdIncomingKey{})` (grpc v1.84.0 `metadata/metadata.go:268-282`: `md, ok :=
ctx.Value(mdIncomingKey{}).(MD)`, then a copy with lower-case keys), so its result is a function of
that value: `(nil, false)` for a value that is not an `MD` (both `none`), else the same `MD`'s
copy; and the `MD` grpc's transport stores there is never written after (`transportMD`). Concludes
only from equal values: nothing is said of contexts whose values differ. -/
axiom metadata.incomingOf_of_value (c c' : GoInterfaceOk) (v : GoInterface) :
    context.valueAt (GF := GF) c metadata.mdIncomingKeyAny (· = v) ∗
      context.valueAt c' metadata.mdIncomingKeyAny (· = v) ⊢
    ⌜metadata.incomingOf (GoInterface.ok c) = metadata.incomingOf (GoInterface.ok c')⌝

end value
end EtcdGrove
end Perennial

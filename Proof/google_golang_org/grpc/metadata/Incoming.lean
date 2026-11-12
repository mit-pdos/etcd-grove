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
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace metadata

/-- **The incoming metadata of the context `ctx`** (opaque, see the file header): `none` if it
has none, else each key's values. -/
opaque incomingOf [GooseExts] : GoInterface → Option (GoString → Option (List GoString))

end metadata

section link
open Iris Iris.BI
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- (TRUSTED; k8s 7f-4, B1's revision of T-b) **A `*cancelCtx` carries its parent's incoming
metadata**: a `*cancelCtx` `c` whose `Context` field holds `p` (`ctxField c ↦□ p`: written once, by
`propagateCancel`, before `WithCancel` returns the context) has `p`'s incoming metadata.
`metadata.FromIncomingContext(x)` (grpc v1.84.0 `metadata/metadata.go:268-282`) is a function of
`x.Value(mdIncomingKey{})`, and `(*cancelCtx).Value(key)` for a key other than `&cancelCtxKey` is
`value(c.Context, key)` (Go `src/context/context.go`), which answers as `p.Value(key)` does:
`value` walks `*valueCtx`/`*cancelCtx`/`*timerCtx` links by their fields, as their own `Value`
methods do, and calls `Value` on a context of any other type.

Why it cannot equate unrelated contexts (the review's `loopCtx`, which refuted T-b): the premise is
a persistent points-to of a `*cancelCtx`'s field, not a `Value` WP, and a points-to determines its
value (`incomingOf_cancelCtx_parent_unique`). So the equations this axiom gives relate each
`*cancelCtx` to its one parent only: two contexts are equated only when they lie on one chain of
`*cancelCtx` parent links up to the same root context. A context `L` whose `Value` loops is a root
(its type is not `*cancelCtx`), and is equated only with `*cancelCtx`s built over it, whose `Value`
then loops too (so `FromIncomingContext` on them never returns, as on `L`); grpc's run context and
`Background()` are distinct roots, and nothing equates them. -/
axiom incomingOf_cancelCtx (c : Loc) (p : GoInterfaceOk) :
    _root_.Perennial.context.ctxField c ↦□ (GoInterface.ok p) ⊢ (iprop(⌜metadata.incomingOf
      (GoInterface.ok (interface.mk (go.GoType.PointerType _root_.Perennial.context.cancelCtx.ty) #c)) =
      metadata.incomingOf (GoInterface.ok p)⌝) : IProp GF)

/-- **`incomingOf_cancelCtx` relates a `*cancelCtx` to one parent only**: two persistent points-tos
of its `Context` field agree. -/
theorem incomingOf_cancelCtx_parent_unique (c : Loc) (p1 p2 : GoInterfaceOk) :
    _root_.Perennial.context.ctxField c ↦□ (GoInterface.ok p1) ∗
      _root_.Perennial.context.ctxField c ↦□ (GoInterface.ok p2) ⊢ (iprop(⌜p1 = p2⌝) : IProp GF) := by
  iintro ⟨H1, H2⟩
  icombine H1 H2 gives %h
  ipureintro
  injection h

end link
end EtcdGrove
end Perennial

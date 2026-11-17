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
`metadata.incomingKept ci` (grpc's run context's `*cancelCtx` children carry its metadata) is a
per-run fact grpc's stream delivery gives (`srvRawStreamIs`).
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

/-- **`ci`'s `*cancelCtx` children carry its incoming metadata** (persistent; incomingof Part A,
approved by the user 2026-11-17 via etcd-grove-03; replaces the axiom `incomingOf_cancelCtx`, refuted
by `crossWorld`: `notes/axiom-review/incomingof.md`): every `*cancelCtx` `c` whose `Context` field
holds `ci` (`ctxField c ↦□ ci`: `WithCancel(ci)`'s `propagateCancel` writes the field before
returning, Go `src/context/context.go:477,514`; the `afterFuncer` branch that rewrites it to a
`stopCtx{ci, ...}` leaves no persistent points-to at `ci`, and such a context answers `Value` as `ci`
anyway) answers `metadata.FromIncomingContext` as `ci` does: `FromIncomingContext(x)` (grpc v1.84.0
`metadata/metadata.go:268-282`) is a function of `x.Value(mdIncomingKey{})`, and
`(*cancelCtx).Value(key)` for a key other than `&cancelCtxKey` is `value(c.Context, key)`, which
answers as `ci.Value(key)` (Go test `examples/axiomcx/incomingof` `TestWrapperInheritsIncoming`).

Not an axiom and not provable: a definition, given only as a conjunct of grpc's trusted delivery of
a stream's run context (`srvRawStreamIs`, in the post of the uninterpreted `acceptRun`), so it is a
claim about the one run that reaches that post. Its conclusion is a pure fact about the opaque
`incomingOf`, so no proof can build it (in a fresh heap or otherwise), and the old axiom's
`crossWorld` refutation (which built its antecedent, a bare points-to, at any address and content)
has no antecedent to build. Two run contexts `ci1`, `ci2` of one run are related by nothing: each
`*cancelCtx` has one `Context` cell, and two persistent points-tos of it agree. -/
def metadata.incomingKept (ci : GoInterfaceOk) : IProp GF :=
  iprop(□ ∀ c : Loc, _root_.Perennial.context.ctxField c ↦□ (GoInterface.ok ci) -∗
    ⌜metadata.incomingOf (GoInterface.ok (interface.mk
        (go.GoType.PointerType _root_.Perennial.context.cancelCtx.ty) #c)) =
      metadata.incomingOf (GoInterface.ok ci)⌝)

instance metadata.incomingKept_persistent (ci : GoInterfaceOk) :
    Persistent (metadata.incomingKept (GF := GF) ci) := by
  unfold metadata.incomingKept; infer_instance

end link
end EtcdGrove
end Perennial

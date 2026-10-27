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
end EtcdGrove
end Perennial

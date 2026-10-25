/-
`metadata.FromIncomingContext` (grpc, `metadata/metadata.go`): the trust boundary (grpc's
`metadata` is types and names only). Lean-first (no Rocq counterpart; unit P2: the auth store's
`AuthInfoFromCtx` reads the token from it).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.auth.Base
public import Proof.google_golang_org.grpc.metadata.Incoming

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI google_golang_org.grpc

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `metadata.FromIncomingContext(ctx)`: `(md, ok)`; `ok` exactly when the context has incoming
metadata (`metadata.incomingOf ctx`, the auth plan's E2c, 2026-10-25), and then `md` is a fresh map
(grpc copies the context's metadata: `out[key] = copyOf(v)`) with that metadata's keys, each value
a fresh slice of that key's strings, **at least one**. The last is narrower than grpc's code, which
copies whatever the context holds: it is true of the metadata grpc's transports put in a request's
context (each key from at least one header field), not of a context built with
`metadata.NewIncomingContext(ctx, MD{k: {}})`, on which etcd's `AuthInfoFromCtx` panics (`ts[0]`;
`issues/etcd-auth-token-md-empty.md`). -/
abbrev metadata.FromIncomingContext.spec : Prop :=
  ∀ (ctx : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc.metadata }}
    (App (Val (@! google_golang_org.grpc.metadata.FromIncomingContext)) (Val #ctx))
  {{ (md : GoMap) (ok : Bool), RET (PairV #md #ok);
      ⌜ok = false ∧ metadata.incomingOf ctx = none⌝ ∨
      ∃ (md0 : GoString → Option (List GoString)) (m : GMap GoString GoSlice),
        ⌜ok = true ∧ metadata.incomingOf ctx = some md0 ∧ ∀ k, m !! k = none ↔ md0 k = none⌝ ∗
        md ↦$ m ∗
        [∗map] k ↦ sl ∈ m, ∃ vs : List GoString, sl ↦* vs ∗ ⌜vs ≠ []⌝ ∗ ⌜md0 k = some vs⌝ }}

end spec

end EtcdGrove
end Perennial

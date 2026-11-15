/-
`metadata.FromIncomingContext` (grpc, `metadata/metadata.go`): the trust boundary (grpc's
`metadata` is types and names only). Lean-first (no Rocq counterpart; unit P2: the auth store's
`AuthInfoFromCtx` reads the token from it).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.auth.Base
public import Proof.google_golang_org.grpc.metadata.Incoming
public import Proof.context.LibKeys

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI google_golang_org.grpc

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `metadata.FromIncomingContext(ctx)`: `(md, ok)`; `ok` exactly when the context has incoming
metadata (`metadata.incomingOf ctx`, the auth plan's E2c, 2026-10-25), and then `md` is a fresh map
(grpc copies the context's metadata: `out[key] = copyOf(v)`) with that metadata's keys, each value
a fresh slice of that key's strings, **at least one**. For a context whose `Value(mdIncomingKey{})`
returns one value on every call, not an `MD` or the transport's (`metadata.incomingCtxOk`,
premise-fixes-8 S2): the metadata is a function of the context (`incomingOf`), and a transport `MD`
has lower-case keys, each with at least one value (`transportMD`), so `vs ≠ []` holds. A context
built with `metadata.NewIncomingContext(ctx, MD{k: {}})` (on which etcd's `AuthInfoFromCtx` panics,
`ts[0]`; `nonissues/etcd-auth-token-md-empty.md`) or whose `Value` panics is excluded by the premise
(`examples/premisefix/ctxvalue`). -/
abbrev metadata.FromIncomingContext.spec : Prop :=
  ∀ (ctx : GoInterfaceOk),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc.metadata ∗
      metadata.incomingCtxOk ctx }}
    (App (Val (@! google_golang_org.grpc.metadata.FromIncomingContext)) (Val #(GoInterface.ok ctx)))
  {{ (md : GoMap) (ok : Bool), RET (PairV #md #ok);
      ⌜ok = false ∧ metadata.incomingOf (GoInterface.ok ctx) = none⌝ ∨
      ∃ (md0 : GoString → Option (List GoString)) (m : GMap GoString GoSlice),
        ⌜ok = true ∧ metadata.incomingOf (GoInterface.ok ctx) = some md0 ∧
          ∀ k, m !! k = none ↔ md0 k = none⌝ ∗
        md ↦$ m ∗
        [∗map] k ↦ sl ∈ m, ∃ vs : List GoString, sl ↦* vs ∗ ⌜vs ≠ []⌝ ∗ ⌜md0 k = some vs⌝ }}

end spec

end EtcdGrove
end Perennial

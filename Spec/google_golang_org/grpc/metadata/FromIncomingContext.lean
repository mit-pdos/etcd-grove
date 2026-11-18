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
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `metadata.FromIncomingContext(ctx)`: `(md, ok)`, for a context whose incoming metadata is `md`
(`metadata.ctxInMD ctx md`: `ctx.Value(mdIncomingKey{})` returns one value `v` on every call, Perennial's
chain, and `v` is not an `MD` (`md = none`) or an `MD` grpc's transport made holding `md = some f`, the
leaf `metadata.transportMDRaw`). `ok` exactly when `md` is `some md0`, and then the result is a fresh map
(grpc copies the context's metadata: `out[key] = copyOf(v)`, `metadata/metadata.go:268-282`) with `md0`'s
keys (Go lower-cases each key, `metadata.go:278`, a no-op on a transport `MD`, whose keys are lower case),
each value a fresh slice of that key's strings, at least one (a transport `MD` has at least one value per
key; independent attack, `/shared/tmp/perheap/c1a/attack-fic.md`). Every pure fact is about the parameter `md` and the returned values (perheap, (I3)). A context
built with `metadata.NewIncomingContext(ctx, MD{k: {}})` (on which etcd's `AuthInfoFromCtx` panics, `ts[0]`;
`nonissues/etcd-auth-token-md-empty.md`) or whose `Value` panics has no `ctxInMD` (`examples/premisefix/ctxvalue`). -/
abbrev metadata.FromIncomingContext.spec : Prop :=
  ∀ (ctx : GoInterfaceOk) (md : Option (GoString → Option (List GoString))),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc.metadata ∗ metadata.ctxInMD ctx md }}
    (App (Val (@! google_golang_org.grpc.metadata.FromIncomingContext)) (Val #(GoInterface.ok ctx)))
  {{ (mp : GoMap) (ok : Bool), RET (PairV #mp #ok);
      ⌜ok = false ∧ md = none⌝ ∨
      ∃ (md0 : GoString → Option (List GoString)) (m : GMap GoString GoSlice),
        ⌜ok = true ∧ md = some md0 ∧ ∀ k, m !! k = none ↔ md0 k = none⌝ ∗
        mp ↦$ m ∗
        [∗map] k ↦ sl ∈ m, ∃ vs : List GoString, sl ↦* vs ∗ ⌜vs ≠ []⌝ ∗ ⌜md0 k = some vs⌝ }}

end spec

end EtcdGrove
end Perennial

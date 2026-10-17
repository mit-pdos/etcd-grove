/-
`metadata.FromOutgoingContext` (grpc, `metadata/metadata.go`): the trust boundary (grpc's
`metadata` is types and names only). Lean-first (no Rocq counterpart; etcd#22291, the lease
client's `lessor.closeRequireLeader` reads whether a keep-alive's context asks for a leader).
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI google_golang_org.grpc

/-- **A context whose outgoing metadata is stable** (uninterpreted): `ctx` is a non-nil context
whose `Value(mdOutgoingKey{})` does not panic and whose outgoing metadata never changes (grpc's
`NewOutgoingContext(ctx, md)` keeps `md` itself, not a copy, so a caller that mutates `md`
afterwards changes what later calls return) and has no two keys equal up to case (which
`FromOutgoingContext` lowercases and merges in map-iteration order). A premise on the contexts a
caller passes, not a fact of grpc: nothing here proves it of a context. -/
opaque metadata.outgoingStable [FfiSyntax] : GoInterface → Prop

/-- **The outgoing metadata of a context** (uninterpreted): what `FromOutgoingContext(ctx)` copies
out of a stable `ctx`, `none` if `ctx` carries none. -/
opaque metadata.outgoingMD [FfiSyntax] : GoInterface → Option (GMap GoString (List GoString))

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `metadata.FromOutgoingContext(ctx)`, for a stable `ctx` (`outgoingStable ctx`): `(md, ok)`.
With no outgoing metadata in `ctx` (`outgoingMD ctx = none`), `ok` is false; otherwise `ok` is
true and `md` is a fresh map (grpc copies: `out := make(MD, ...)`, each value a fresh slice,
`copyOf` or an `append` onto it) with the keys and values of `outgoingMD ctx`. -/
abbrev metadata.FromOutgoingContext.spec : Prop :=
  ∀ (ctx : GoInterface), metadata.outgoingStable ctx →
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc.metadata }}
    (App (Val (@! google_golang_org.grpc.metadata.FromOutgoingContext)) (Val #ctx))
  {{ (md : GoMap) (ok : Bool), RET (PairV #md #ok);
      match metadata.outgoingMD ctx with
      | none => ⌜ok = false⌝
      | some mv => ⌜ok = true⌝ ∗ ∃ m : GMap GoString GoSlice, md ↦$ m ∗
          ⌜∀ k, (m !! k).isSome = (mv !! k).isSome⌝ ∗
          [∗map] k ↦ sl ∈ m, ∃ vs : List GoString, sl ↦* vs ∗ ⌜mv !! k = some vs⌝ }}

end spec

end EtcdGrove
end Perennial

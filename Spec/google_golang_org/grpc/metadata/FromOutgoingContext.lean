/-
`metadata.FromOutgoingContext` (grpc, `metadata/metadata.go`): the trust boundary (grpc's
`metadata` is types and names only). Lean-first (no Rocq counterpart; item 1, the client lease:
`client/v3`'s `lessor.closeRequireLeader` reads a keep-alive context's outgoing metadata with it).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvLease
public import Perennial.Proof.context

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

/-- `metadata.FromOutgoingContext(ctx)` on a context (`context.isContext`): `(md, ok)`; if `ok`,
`md` is a fresh map (grpc builds it: `out := make(MD, mdSize)`, each value `copyOf(v)` or
appended to from the context's `rawMD`), each of its values a fresh slice of strings (any number,
none included). grpc's code reads the context's `Value(mdOutgoingKey{})` (an unexported key: only
grpc's `NewOutgoingContext`/`AppendToOutgoingContext` store a `rawMD` under it) and asserts it
with `, ok`; its panic on an odd-length `added` list is unreachable (`AppendToOutgoingContext`
panics first on an odd number of arguments). Like `context.ValueKeepAlive`, it assumes the
context's `Value` returns at a key it does not know. -/
abbrev metadata.FromOutgoingContext.spec : Prop :=
  ∀ (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc.metadata ∗ context.isContext ctx cd }}
    (App (Val (@! google_golang_org.grpc.metadata.FromOutgoingContext)) (Val #(GoInterface.ok ctx)))
  {{ (md : GoMap) (ok : Bool), RET (PairV #md #ok);
      ⌜ok = false⌝ ∨ ∃ m : GMap GoString GoSlice, md ↦$ m ∗
        [∗map] _k ↦ sl ∈ m, ∃ vs : List GoString, sl ↦* vs }}

end spec

end EtcdGrove
end Perennial

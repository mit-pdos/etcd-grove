/-
`credentials.NewContextWithRequestInfo(ctx, ri)` (grpc's `credentials/credentials.go`):
`context.WithValue(ctx, requestInfoKey{}, ri)`.

**Not proved** (phase 7 S2 core, 2026-11-23): the trusted `context.WithValue` axiom
(`Proof/context/WithValue.lean`) lists the key types it accepts and `requestInfoKey` is not one; the
user is deciding between translating `WithValue` in Perennial and widening the axiom. Until then this
spec is taken as a callee-spec hypothesis by the proofs that call it (`createHeaderFields`), stated
as `WithValue`'s proof would give it, and no proof file exists. It is the spec of the real body: the
`Value` of the new context at the key `requestInfoKey{}` is `ri` (as an `any`), at any other key the
parent's; a context description of the parent is one of the child with the key added.
-/
module

public import Perennial.Proof.context
public import GeneratedProof.google_golang_org.grpc.credentials
public import Proof.go_etcd_io.etcd.cache.v3.Base

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- The key `NewContextWithRequestInfo` stores the request's information at: `requestInfoKey{}` as
an `any`. -/
abbrev credentials.requestInfoKeyIface : GoInterface :=
  interface.mkOk google_golang_org.grpc.credentials.requestInfoKey.ty
    #(zero_val google_golang_org.grpc.credentials.requestInfoKey)

/-- A context's values with the request's information `ri` stored at `requestInfoKey{}`. -/
abbrev credentials.withRequestInfo (vs : GMap GoInterface GoInterface)
    (ri : google_golang_org.grpc.credentials.RequestInfo) : GMap GoInterface GoInterface :=
  GMap.insert credentials.requestInfoKeyIface
    (interface.mkOk google_golang_org.grpc.credentials.RequestInfo.ty #ri) vs

/-- **`NewContextWithRequestInfo(ctx, ri)`** of a non-nil context returns a non-nil context `c'`:
its `Value(k)` is `ri` (as an `any`) at `k = requestInfoKey{}` and the parent's `Value(k)` at every
other key (stated, as `context.WithValue.spec` does, for any property `R` of the result); and a
description `cd` of the parent describes `c'` with the key added to its values. -/
abbrev credentials.NewContextWithRequestInfo.spec : Prop :=
  ∀ (parent : GoInterfaceOk) (ri : google_golang_org.grpc.credentials.RequestInfo),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc.credentials }}
    (App (App (Val (@! google_golang_org.grpc.credentials.NewContextWithRequestInfo))
      (Val #(GoInterface.ok parent))) (Val #ri))
  {{ (c' : GoInterfaceOk), RET #(GoInterface.ok c');
      □ (∀ (k : GoInterface) (R : GoInterface → Prop),
          ⌜k = credentials.requestInfoKeyIface →
            R (interface.mkOk google_golang_org.grpc.credentials.RequestInfo.ty #ri)⌝ -∗
          (⌜k ≠ credentials.requestInfoKeyIface⌝ -∗
            {{ True }} (App (Val #(methods parent.ty go!"Value" parent.v)) (Val #k))
            {{ (w : GoInterface), RET #w; ⌜R w⌝ }}) -∗
          {{ True }} (App (Val #(methods c'.ty go!"Value" c'.v)) (Val #k))
          {{ (w : GoInterface), RET #w; ⌜R w⌝ }}) ∗
      □ (∀ cd : context.ContextDesc (IProp GF), context.isContext parent cd -∗
          context.isContext c' { cd with Values := credentials.withRequestInfo cd.Values ri }) }}

end spec

end EtcdGrove
end Perennial

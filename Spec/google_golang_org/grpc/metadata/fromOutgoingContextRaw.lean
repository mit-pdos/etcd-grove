/-
`metadata.fromOutgoingContextRaw(ctx)` (grpc's `metadata`, translated with its body; phase 7 S2 core,
2026-11-23): what grpc's transport reads of a context's outgoing metadata, through grpc's package
variable `metadataFromOutgoingContextRaw` (`createHeaderFields`).
-/
module

public import Proof.context.LibKeys

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **`fromOutgoingContextRaw(ctx)`** of a context whose `Value(mdOutgoingKey{})` returns `v`
(`context.valueAt`): `(raw.md, raw.added, true)` if `v` is a `rawMD` `raw`, otherwise `ok = false`
(Go: `raw, ok := ctx.Value(mdOutgoingKey{}).(rawMD); if !ok { return nil, nil, false }`). The premise
says that a `v` of dynamic type `rawMD` holds a `rawMD` value, as every Go value of that type does
(GooseLang's interface values do not carry it). -/
abbrev metadata.fromOutgoingContextRaw.spec : Prop :=
  ∀ (ctx : GoInterfaceOk) (v : GoInterface),
  (∀ vi : GoInterfaceOk, v = GoInterface.ok vi → vi.ty = google_golang_org.grpc.metadata.rawMD.ty →
    ∃ r : google_golang_org.grpc.metadata.rawMD, vi.v = #r) →
  {{ context.valueAt (GF := GF) ctx metadata.mdOutgoingKeyAny (· = v) }}
    (App (Val (@! google_golang_org.grpc.metadata.fromOutgoingContextRaw))
      (Val #(GoInterface.ok ctx)))
  {{ (md : GoMap) (added : GoSlice) (ok : Bool), RET (PairV (PairV #md #added) #ok);
      ⌜if ok then v = interface.mkOk google_golang_org.grpc.metadata.rawMD.ty
          #(google_golang_org.grpc.metadata.rawMD.mk md added)
        else ∀ vi : GoInterfaceOk, v = GoInterface.ok vi →
          vi.ty ≠ google_golang_org.grpc.metadata.rawMD.ty⌝ }}

end spec

end EtcdGrove
end Perennial

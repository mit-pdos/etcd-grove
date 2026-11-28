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
(`context.valueAt`): with `ro = some r`, `v` is the `rawMD` `r` and the call returns `(r.md, r.added,
true)`; with `ro = none`, `v` is no `rawMD` and `ok` is `false` (Go: `raw, ok :=
ctx.Value(mdOutgoingKey{}).(rawMD); if !ok { return nil, nil, false }`). The caller names the `rawMD`
(GooseLang's values do not say that a value of dynamic type `rawMD` is one). -/
abbrev metadata.fromOutgoingContextRaw.spec : Prop :=
  ∀ (ctx : GoInterfaceOk) (v : GoInterface) (ro : Option google_golang_org.grpc.metadata.rawMD),
  (match ro with
    | some r => v = interface.mkOk google_golang_org.grpc.metadata.rawMD.ty #r
    | none => ∀ vi : GoInterfaceOk, v = GoInterface.ok vi →
        vi.ty ≠ google_golang_org.grpc.metadata.rawMD.ty) →
  {{ context.valueAt (GF := GF) ctx metadata.mdOutgoingKeyAny (· = v) }}
    (App (Val (@! google_golang_org.grpc.metadata.fromOutgoingContextRaw))
      (Val #(GoInterface.ok ctx)))
  {{ (md : GoMap) (added : GoSlice) (ok : Bool), RET (PairV (PairV #md #added) #ok);
      ⌜match ro with
        | some r => ok = true ∧ md = r.md' ∧ added = r.added'
        | none => ok = false⌝ }}

end spec

end EtcdGrove
end Perennial

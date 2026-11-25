/-
`wrapperspb.String(v)` (protobuf-go, translated with its body): `&StringValue{Value: v}`.
Lean-first (no Rocq counterpart).
-/
module

public import Proof.google_golang_org.protobuf.types.known.wrapperspb.PerTypeStringValue
public import Proof.google_golang_org.protobuf.types.known.wrapperspb.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI google_golang_org.protobuf.types.known

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [pkg_wr : google_golang_org.protobuf.types.known.wrapperspb.Assumptions]

/-- `wrapperspb.String(v)`: a fresh `*StringValue` holding `v`, with no unknown fields. -/
abbrev wrapperspb.String.spec : Prop :=
  ∀ (v : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.protobuf.types.known.wrapperspb }}
    (App (Val (@! wrapperspb.String)) (Val #v))
  {{ (l : Loc), RET #l; ∃ x : wrapperspb.StringValue, l ↦ x ∗
      ⌜x.Value' = v ∧ x.unknownFields' = slice.nil⌝ }}

end spec

end EtcdGrove
end Perennial

/- Lean-first (no Rocq counterpart).

`wrapperspb.String(v)` (`types/known/wrapperspb/wrappers.pb.go`, translated with its body): a new
`*StringValue` holding `v`, a sender's message (`stringValueSend`, `PerTypeStringValue.lean`) for a
`v` below `stringValueMax`.
-/
module

public import Proof.google_golang_org.protobuf.types.known.wrapperspb.PerTypeStringValue

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : google_golang_org.protobuf.types.known.wrapperspb.Assumptions]

/-- See the file header. -/
abbrev google_golang_org.protobuf.types.known.wrapperspb.String.spec : Prop :=
  ∀ (v : GoString), v.length < EtcdGrove.stringValueMax →
  {{ (True : IProp GF) }}
    (App (Val (@! google_golang_org.protobuf.types.known.wrapperspb.String)) (Val #v))
  {{ (l : Loc), RET #l; EtcdGrove.stringValueSend l v }}

end spec

end Perennial

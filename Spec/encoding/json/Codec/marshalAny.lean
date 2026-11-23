/-
`marshalAny(v)` (the encoding/json model's per-type dispatch, `model.go`): by `v`'s dynamic
type's method set, its `JSONModelMarshalPtr` or `JSONModelMarshal`, else the registered codec
(`marshalVia J F v`: the route's contract `J`), with `J.enc v Ψ`: `Marshal`'s outcome (`marshalRet`)
(mit-pdos/etcd-grove#24, J2/J3).
Lean-first (no Rocq counterpart).
-/
module

public import Proof.encoding.json.Registry

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace encoding.json

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : encoding.json.Assumptions]

/-- See the file header. -/
abbrev marshalAny.spec : Prop :=
  ∀ (J : models_lab.jsoncodec.JsonCodec GF) (F : List w8 → Bool → w64 × w64) (v : GoInterface)
    (Ψ : Option (List w8) → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.encoding.json ∗ marshalVia J F v ∗ J.enc v Ψ }}
    (App (Val (@! encoding.json.marshalAny)) (Val #v))
  {{ (s : GoSlice) (err : GoInterface), RET (PairV #s #err); marshalRet (GF := GF) Ψ s err }}

end spec

end encoding.json
end Perennial

/-
`pbcodec.AppendTag(b, num, typ)`: `b` with the tag of field `num` of wire type `typ` appended
(`EtcdGrove.Wire.tag`, the minimal varint of `num * 8 + typ`; `protowire.AppendTag`), for a field
number below `2^61` and a wire type below 8 (every caller's: generated code passes constants).
Lean-first (#37 stage S3).
-/
module

public import Net.Proof.models_lab.pbcodec.WireDefs

@[expose] public section

set_option linter.iris.dupNamespace false

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace models_lab.pbcodec

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : models_lab.pbcodec.Assumptions]

/-- See the file header. -/
abbrev AppendTag.spec : Prop :=
  ∀ (b : GoSlice) (bs : List w8) (num typ : w64), uint.nat num < 2 ^ 61 → uint.nat typ < 8 →
  {{ (b ↦* bs ∗ ownSliceCap w8 b (DFrac.own 1) : IProp GF) }}
    (App (App (App (Val (@! models_lab.pbcodec.AppendTag)) (Val #b)) (Val #num)) (Val #typ))
  {{ (b' : GoSlice), RET #b'; b' ↦* (bs ++ EtcdGrove.Wire.tag (uint.nat num) (uint.nat typ)) ∗
      ownSliceCap w8 b' (DFrac.own 1) }}

end spec

end models_lab.pbcodec
end Perennial

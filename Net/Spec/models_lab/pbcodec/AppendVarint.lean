/-
`pbcodec.AppendVarint(b, v)`: `b` with the minimal varint of `v` appended (`EtcdGrove.varintEnc`;
`protowire.AppendVarint`). The result may share `b`'s array (Go's `append`). Lean-first (#37 stage S3).
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
abbrev AppendVarint.spec : Prop :=
  ∀ (b : GoSlice) (bs : List w8) (v : w64),
  {{ (b ↦* bs ∗ ownSliceCap w8 b (DFrac.own 1) : IProp GF) }}
    (App (App (Val (@! models_lab.pbcodec.AppendVarint)) (Val #b)) (Val #v))
  {{ (b' : GoSlice), RET #b'; b' ↦* (bs ++ EtcdGrove.varintEnc (uint.nat v)) ∗
      ownSliceCap w8 b' (DFrac.own 1) }}

end spec

end models_lab.pbcodec
end Perennial

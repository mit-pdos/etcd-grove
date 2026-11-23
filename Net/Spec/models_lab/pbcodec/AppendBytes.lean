/-
`pbcodec.AppendBytes(b, v)`: `b` with `v` appended length-delimited (its length as the minimal
varint, then its bytes: `EtcdGrove.Wire.FVal.payload (.len vs)`; `protowire.AppendBytes`); `v` is
read, not kept. Lean-first (#37 stage S3).
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
abbrev AppendBytes.spec : Prop :=
  ∀ (b : GoSlice) (bs : List w8) (v : GoSlice) (dq : DFrac) (vs : List w8),
  {{ (b ↦* bs ∗ ownSliceCap w8 b (DFrac.own 1) ∗ v ↦*{dq} vs : IProp GF) }}
    (App (App (Val (@! models_lab.pbcodec.AppendBytes)) (Val #b)) (Val #v))
  {{ (b' : GoSlice), RET #b'; b' ↦* (bs ++ EtcdGrove.Wire.FVal.payload (.len vs)) ∗
      ownSliceCap w8 b' (DFrac.own 1) ∗ v ↦*{dq} vs }}

end spec

end models_lab.pbcodec
end Perennial

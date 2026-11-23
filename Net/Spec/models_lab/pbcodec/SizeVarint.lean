/-
`pbcodec.SizeVarint(v)`: the length of the minimal varint of `v` (`EtcdGrove.varintSize`, the
length of `varintEnc`, what `AppendVarint` writes; `protowire.SizeVarint`). Lean-first (#37 stage S3).
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
abbrev SizeVarint.spec : Prop :=
  ∀ (v : w64),
  {{ (True : IProp GF) }}
    (App (Val (@! models_lab.pbcodec.SizeVarint)) (Val #v))
  {{ RET #(W64 (EtcdGrove.varintSize (uint.nat v))); True }}

end spec

end models_lab.pbcodec
end Perennial

/-
`modelIndexByte(s, c)` (the model's `strings.IndexByte`, `textproto_model.go`): the index of the
first `c` in `s`, or `-1` (`idxByte`); `s` is shorter than `2 ^ 63` (as every Go string: its
`len`). Proved in `Net/Proof/net/http/modelIndexByte.lean`.
-/
module

public import Net.Proof.net.http.Defs

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace net.http

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : net.http.Assumptions]

/-- See the file header. -/
abbrev modelIndexByte.spec : Prop :=
  ∀ (s : GoString) (c : w8),
  {{ (True : IProp GF) }}
    (App (App (Val (@! net.http.modelIndexByte)) (Val #s)) (Val #c))
  {{ RET #(idxByte s c); ⌜s.length < 2 ^ 63⌝ }}

end spec

end net.http
end Perennial

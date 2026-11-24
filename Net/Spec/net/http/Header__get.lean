/-
`h.get(key)` on an `http.Header` map `h` (`header.go`) whose `key` slice's values are owned
(`hdrVals`, `Net/Proof/net/http/Defs.lean`): the slice's first value, `""` if `key` has no entry;
the map only read (any fraction). Proved in `Net/Proof/net/http/Header__get.lean`.
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
abbrev Header.get.spec : Prop :=
  ∀ (h : Loc) (dq : DFrac) (ms : GMap GoString GoSlice) (key : GoString),
  {{ (h ↦${dq} ms ∗ hdrVals ms key : IProp GF) }}
    (App (Val #(methods net.http.Header.ty go!"get" #h)) (Val #key))
  {{ (v : GoString), RET #v; h ↦${dq} ms ∗ hdrVals ms key ∗ ⌜ms !! key = none → v = go!""⌝ }}

end spec

end net.http
end Perennial

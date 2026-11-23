/-
`fixLength(isResponse, status, requestMethod, header, chunked)` for a response to a request other than
`HEAD`, not chunked, with an empty header (no `Content-Length`): no error, and `0` (the statuses
without a body: 1xx, 204, 304) or `-1` (to the connection's end), the header still empty. Proved in
`Net/Proof/net/http/fixLength.lean`.
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
abbrev fixLength.spec : Prop :=
  ∀ (status : w64) (method : GoString) (h : Loc),
  {{ (⌜method ≠ go!"HEAD"⌝ ∗ h ↦$ (∅ : GMap GoString GoSlice) : IProp GF) }}
    (App (App (App (App (App (Val (@! net.http.fixLength)) (Val #true)) (Val #status)) (Val #method))
      (Val #h)) (Val #false))
  {{ (n : w64), RET (PairV #n #interface.nil); ⌜n = W64 0 ∨ n = W64 (-1)⌝ ∗
      h ↦$ (∅ : GMap GoString GoSlice) }}

end spec

end net.http
end Perennial

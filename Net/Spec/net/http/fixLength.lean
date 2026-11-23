/-
`fixLength(isResponse, status, requestMethod, header, chunked)`, not chunked, the header map without
`"Content-Length"`, for a response to a request other than `HEAD` or for a request: no error, and `0`
(a request; a response's statuses without a body: 1xx, 204, 304) or, for a response, `-1` (to the
connection's end); the header unchanged. Proved in `Net/Proof/net/http/fixLength.lean`.
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
  ∀ (isResp : Bool) (status : w64) (method : GoString) (h : Loc) (ms : GMap GoString GoSlice),
  {{ (⌜isResp = true → method ≠ go!"HEAD"⌝ ∗ ⌜ms !! go!"Content-Length" = none⌝ ∗ h ↦$ ms : IProp GF) }}
    (App (App (App (App (App (Val (@! net.http.fixLength)) (Val #isResp)) (Val #status)) (Val #method))
      (Val #h)) (Val #false))
  {{ (n : w64), RET (PairV #n #interface.nil); ⌜n = W64 0 ∨ (isResp = true ∧ n = W64 (-1))⌝ ∗
      h ↦$ ms }}

end spec

end net.http
end Perennial

/-
`modelParseRequestURI(rawurl)` (the model's `url.ParseRequestURI`, `textproto_model.go`) on a `reqPath`
(`Net/Proof/net/http/RequestDefs.lean`: `/` and bytes net/url leaves alone): a fresh `*url.URL` whose
path is `rawurl` and every other field zero, and a `nil` error (Go's `parse(rawurl, true)` on such a
URI). Proved in `Net/Proof/net/http/modelParseRequestURI.lean`.
-/
module

public import Net.Proof.net.http.RequestDefs

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
abbrev modelParseRequestURI.spec : Prop :=
  ∀ (s : GoString),
  {{ (⌜reqPath s⌝ : IProp GF) }}
    (App (Val (@! net.http.modelParseRequestURI)) (Val #s))
  {{ (u : Loc), RET (PairV #u #interface.nil);
      u ↦ { (_root_.Perennial.zero_val net.url.URL) with Path' := s } }}

end spec

end net.http
end Perennial

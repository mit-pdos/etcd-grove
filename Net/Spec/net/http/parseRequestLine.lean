/-
`parseRequestLine(line)` (`request.go`): `parseReqLine line` (`Net/Proof/net/http/RequestDefs.lean`):
the method, the request URI and the protocol, split at the first two spaces, and `true`; or empties
and `false` when there are fewer than two (`strings.Cut`, which needs `strings`' initialization). Proved
in `Net/Proof/net/http/parseRequestLine.lean`.
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
abbrev parseRequestLine.spec : Prop :=
  ∀ (line : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.strings }}
    (App (Val (@! net.http.parseRequestLine)) (Val #line))
  {{ RET (PairV (PairV (PairV #(parseReqLine line).1 #(parseReqLine line).2.1)
        #(parseReqLine line).2.2.1) #(parseReqLine line).2.2.2); True }}

end spec

end net.http
end Perennial

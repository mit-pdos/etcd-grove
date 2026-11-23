/-
The vocabulary of httpguts' specs (Go 1.27.3's vendored `golang.org/x/net/http/httpguts`):

* `tokenTable` (persistent): the package variable `isTokenTable` holds, for each byte `c`, whether it
  is RFC 7230's `tchar` (`fieldByte c`); defined in `Net/Proof/net/http/Defs.lean` (part of net/http's
  `httpEnv`), which this module re-exports.
-/
module

public import Net.Proof.net.http.Defs

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace vendor.golang_org.x.net.http.httpguts

section env
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

end env

end vendor.golang_org.x.net.http.httpguts
end Perennial

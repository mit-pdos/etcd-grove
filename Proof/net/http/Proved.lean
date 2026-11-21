/-
**The HTTP boundary's statements proved over net/http's translated code** (prove-http,
2026-11-20): what `Proof/net/http/Axioms.lean` assumed until then and the translation now has a
body for (`Code/net/http.toml`). `Axioms.lean` imports this file, so the boundary's importers see
the same names.
-/
module

public import Proof.net.http.Boundary

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace http

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.net.http.Assumptions]

/-- `http.StatusText(code)` (`status.go:81`, go1.27.3): a `switch` on the code whose every case
returns a string literal, `""` by default. -/
theorem StatusText_ok : StatusText_spec (GF := GF) := by
  intro code
  wp_start
  wp_auto
  repeat' wp_if_destruct
  all_goals (iapply HΦ; itrivial)

end proof

end http
end EtcdGrove
end Perennial

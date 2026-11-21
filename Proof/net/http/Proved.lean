/-
**The HTTP boundary's statements proved over net/http's translated code** (prove-http,
2026-11-20): what `Proof/net/http/Axioms.lean` assumed until then and the translation now has a
body for (`Code/net/http.toml`); (stdlib2, 2026-11-21) `bytes.NewBuffer` over Perennial's. `Axioms.lean` imports this file, so the boundary's importers see
the same names.
-/
module

public import Proof.net.http.Boundary
public import Perennial.Proof.bytes.Link

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

section buffer
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.bytes.Assumptions]

/-- `bytes.NewBuffer(b)` (`NewBuffer_spec`): Perennial's (stdlib2, 2026-11-21; until then an axiom). -/
theorem NewBuffer_ok : NewBuffer_spec (GF := GF) := by
  intro b bs
  iintro %Φ !> Hb HΦ
  wp_apply _root_.Perennial.bytes.wp_NewBuffer b bs $$ Hb as %l Hl
  iapply HΦ
  unfold readerHas
  iright
  iexists l
  iframe Hl
  ipureintro; rfl

/-- `nil` is a reader of no bytes, an empty request body (`readerHas`'s first case; `NewRequest`'s
`nil` body). (stdlib2, 2026-11-21; until then an axiom.) -/
theorem readerHas_nil : ⊢ readerHas (GF := GF) GoInterface.nil [] := by
  unfold readerHas
  ileft
  ipureintro
  exact ⟨rfl, rfl⟩

end buffer

end http
end EtcdGrove
end Perennial

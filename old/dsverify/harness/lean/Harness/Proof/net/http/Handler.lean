/-
The `*response` methods of the lab's model of `net/http` that handlers call: `Hijack`
(`response.Hijack.spec`, `Proto.lean`).
-/
module

public import Harness.Proof.net.http.Proto

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode NetConn

namespace net.http

section proofs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netConnExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [net.Assumptions] [net.model.Assumptions] [net.http.Assumptions]

set_option goose.wp.extras true

theorem response.Hijack.wp_proof : response.Hijack.spec (GF := GF) (hG := hG) := by
  intro l cv wh
  wp_start as Hl
  wp_auto
  iapply HΦ
  iframe

end proofs

end net.http

end Perennial

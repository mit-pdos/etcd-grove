/-
The proof of `chunkedWriter.Close` (`Net/Spec/net/http/internal/chunkedWriter__Close.lean`):
`io.WriteString(cw.Wire, "0\r\n")` (its spec pending on Perennial: a hypothesis) over the sink's
string-write contract.
-/
module

public import Net.Spec.net.http.internal.chunkedWriter__Close

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace net.http.internal

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : net.http.internal.Assumptions]

theorem chunkedWriter.Close.wp_proof
    (wp_WriteString : EtcdGrove.io.WriteString.spec (GF := GF) (hG := hG)) :
    chunkedWriter.Close.spec (GF := GF) (hG := hG) := by
  intro cw wi W B out
  unfold lastChunk
  wp_start as ⟨Hcw, #Hsink, HW⟩
  iunfold chunkedW at Hcw
  iunfold chunkSink at Hsink
  icases Hsink with ⟨-, #Hstr, -, -⟩
  wp_auto
  wp_apply wp_WriteString wi go!"0\r\n" (W out) (sinkPost W B out go!"0\r\n") $$ [$HW]
    as %n %err Hpost
  · iapply Hstr
  iunfold sinkPost at Hpost
  icases Hpost with (⟨⟨%He, -⟩, HW⟩ | ⟨%He, HB⟩)
  · subst He
    iapply HΦ
    isplitl [Hcw]
    · iunfold chunkedW; iexact Hcw
    ileft
    iframe HW
    ipureintro; rfl
  · iapply HΦ
    isplitl [Hcw]
    · iunfold chunkedW; iexact Hcw
    iright
    iframe HB
    ipureintro; exact He

end proof

end net.http.internal
end Perennial


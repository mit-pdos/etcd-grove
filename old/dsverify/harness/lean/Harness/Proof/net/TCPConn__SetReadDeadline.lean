/-
The proof of `Spec/net/TCPConn__SetReadDeadline.lean`: the promoted method, then the
model's `setDeadline` (`net.wp_setDeadline`).
-/
module

public import Harness.Spec.net.TCPConn__SetReadDeadline

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode NetConn

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netConnExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [net.Assumptions] [net.model.Assumptions]

theorem net.TCPConn.SetReadDeadline.wp_proof :
    net.TCPConn.SetReadDeadline.spec (GF := GF) (hG := hG) := by
  intro c cid side t
  unfold net.ownTCPConn
  wp_start as ⟨%fd, #Hfd, #HFD, #Hc, -⟩
  rw [method_unfold]
  wp_auto
  wp_apply net.wp_setDeadline _ fd cid side (W64 1) (by decide) t $$ [$Hfd $HFD $Hc]
    as %err ⟨%code, #Herr⟩
  ihave %Hn := net.connErr_nil $$ Herr
  iapply HΦ
  iexists code
  iframe Herr
  ipureintro; exact Hn

end proof

end Perennial

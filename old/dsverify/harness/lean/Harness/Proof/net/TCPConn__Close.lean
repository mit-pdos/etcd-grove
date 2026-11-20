/-
The proof of `Spec/net/TCPConn__Close.lean`: the promoted method, then the model over
`NetConn.wp_Close` and `net.wp_connResult`.
-/
module

public import Harness.Spec.net.TCPConn__Close

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

theorem net.TCPConn.Close.wp_proof : net.TCPConn.Close.spec (GF := GF) (hG := hG) := by
  intro c cid side
  unfold net.ownTCPConn
  wp_start as ⟨%fd, #Hfd, #HFD, #Hc, -⟩
  rw [method_unfold]
  wp_auto
  wp_apply net.wp_fdOf $$ Hfd
  wp_apply net.wp_idSide $$ HFD
  wp_apply NetConn.wp_Close cid side $$ Hc as %code -
  wp_apply net.wp_connResult $$ [$HFD] as %err #Herr
  ihave %Hn := net.connErr_nil $$ Herr
  iapply HΦ
  iexists code
  iframe Herr
  ipureintro; exact Hn

end proof

end Perennial

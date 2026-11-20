/-
The proof of `Spec/net/TCPConn__Write.lean`: the promoted method, then the model over
`NetConn.wp_Write`.
-/
module

public import Harness.Spec.net.TCPConn__Write

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

theorem net.TCPConn.Write.wp_proof : net.TCPConn.Write.spec (GF := GF) (hG := hG) := by
  intro c cid side b bs dq P W
  unfold net.ownTCPConn
  wp_start as ⟨⟨%fd, #Hfd, #HFD, #Hc, -⟩, Htok, #HP, Hb⟩
  rw [method_unfold]
  wp_auto
  wp_apply net.wp_fdOf $$ Hfd
  wp_apply net.wp_idSide $$ HFD
  wp_apply net.wp_idSide $$ HFD
  wp_apply wp_bytes_to_string $$ Hb as Hb
  wp_apply NetConn.wp_Write cid side bs P W $$ [$Htok $HP] as %k %code ⟨%Hk, Htok⟩
  wp_apply net.wp_connResult $$ [$HFD] as %err #Herr
  ihave %Hn := net.connErr_nil $$ Herr
  iapply HΦ
  iexists k, code
  iframe Hb Htok Herr
  ipureintro
  exact ⟨rfl, Hk.1, Hn, fun h => Hk.2 (Hn.1 h)⟩

end proof

end Perennial

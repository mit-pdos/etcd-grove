/-
Package `proxy`: `Proxy.NetworkInit` (`startOutgoingLinks`, then `waitForConnections` in a
goroutine with the accept routine's token `netTok γ k`) from its routines' specs
(`NetSpecs.lean`); `Proxy/Results` composes the routines' proofs.
-/
module

public import Dsverify.Proof.raxos.Proxy.NetSpecs

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.raxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open Perennial.raxos.pure Perennial.raxos.msg
open raxos.replica.src

section proofs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [π : NetProtoGS] [qv : hyp.QpVocab GF]
variable [raxos.replica.src.Assumptions]

theorem networkInit_of (wp_wait : waitForConnections.spec (GF := GF) (hG := hG))
    (wp_links : startOutgoingLinks.spec (GF := GF) (hG := hG)) :
    Proxy.NetworkInit.spec (GF := GF) (hG := hG) := by
  intro γ c k pr
  wp_start as ⟨#Hsh, Htok⟩
  wp_auto
  wp_apply wp_links γ c k pr $$ [$Hsh]
  wp_apply wp_fork $$ [Htok]
  · wp_apply wp_wait γ c k pr $$ [$Hsh $Htok]
    itrivial
  wp_end

end proofs

end Perennial.raxos

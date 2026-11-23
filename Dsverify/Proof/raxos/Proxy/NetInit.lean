/-
Package `proxy`: `Proxy.NetworkInit` from its routines' specs (`NetSpecs.lean`), and its proof
(`networkInit_proof`).
-/
module

public import Dsverify.Proof.raxos.Proxy.NetAccept
public import Dsverify.Proof.raxos.Proxy.NetDial
public import Dsverify.Proof.raxos.Proxy.NetListen
public import Dsverify.Proof.raxos.Proxy.NetSend

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
 
  [raxos.replica.src.Assumptions] [raxos.proto.client.Assumptions]
  [raxos.examples.quepaxanet.Assumptions]

theorem networkInit_of (wp_wait : waitForConnections.spec (GF := GF) (hG := hG))
    (wp_links : startOutgoingLinks.spec (GF := GF) (hG := hG)) :
    Proxy.NetworkInit.spec (GF := GF) (hG := hG) := by
  intro γ c k pr
  wp_start as ⟨#Hsh, Htok, Hip⟩
  wp_auto
  wp_apply wp_links γ c k pr $$ [$Hsh]
  wp_apply wp_fork $$ [Htok Hip]
  · wp_apply wp_wait γ c k pr $$ [$Hsh $Htok $Hip]
    itrivial
  wp_end

theorem networkInit_proof : Proxy.NetworkInit.spec (GF := GF) (hG := hG) :=
  networkInit_of (waitForConnections_of connectionListener_proof connectToClient_proof)
    startOutgoingLinks_proof

end proofs

end Perennial.raxos

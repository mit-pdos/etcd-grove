/-
Package `replica`'s sealed slots (interface of stage 2, `notes/stage2-plan.md`): their names and
types are the interface; their bodies are the package's to choose (placeholders until package
`replica` defines them in Prove); clients use them only through the specs of `Replica.lean`.
-/
module

public import Dsverify.Proof.raxos.Replica.Defs

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.raxos


open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open Perennial.raxos.pure Perennial.raxos.msg
open raxos.replica.src

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [π : NetProtoGS] [qv : hyp.QpVocab GF]

/-! ## The server (package `replica`'s slots) -/

/-- After `raxos.New`: replica `k` of the configuration `c`: the proxy, the proposers'
resources, the recorder and the network resources (`Replica/Defs.lean`). -/
def serverNew (γ : QNames) (c : QConf) (k : Nat) (s : Loc) : IProp GF :=
  iprop(srvProxy γ c k s ∗ srvProposers γ c k s ∗ srvRecorder γ c k s)

/-- After `Server.NetworkInit`: the proxy and the proposers' resources. -/
def serverNet (γ : QNames) (c : QConf) (k : Nat) (s : Loc) : IProp GF :=
  iprop(srvProxy γ c k s ∗ srvProposers γ c k s)

/-- After `Server.StartProposers`: the proxy. -/
def serverProp (γ : QNames) (c : QConf) (k : Nat) (s : Loc) : IProp GF := srvProxy γ c k s

end defs

end Perennial.raxos

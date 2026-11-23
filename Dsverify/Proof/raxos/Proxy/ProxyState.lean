/-
Package `proxy`'s definitions of the proxy's state (the bodies of its sealed slots `proxyOwn`,
`proxyShared` are built from them): the resident store, the executed batches, the known batches,
the replicated log, the answers' channel.
-/
module

public import Dsverify.Proof.raxos.Proxy.OwnProp
public import Dsverify.Proof.raxos.Proxy.SharedLoop
public import Dsverify.Proof.raxos.Proxy.SharedNet

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

/-- What the proxy's goroutines share, for good: the invariants and protocols, the store, the
proxy's constant fields and its channels with their elements' predicates. -/
def proxySharedDef (γ : QNames) (c : QConf) (k : Nat) (pr : Loc) : IProp GF :=
  iprop(∃ (hs : raxos.replica.src.Assumptions) (γs : GName)
      (cb bm ebm : Loc),
    sharedFacts γ c k ∗ sharedConsts c k pr ∗ sharedStore γ γs pr cb bm ebm ∗
    (haveI : raxos.replica.src.Assumptions := hs; sharedChans (GF := GF) γ k pr) ∗
    sharedLoop γ k pr ∗ sharedNet γ k pr)

instance proxySharedDef_persistent (γ : QNames) (c : QConf) (k : Nat) (pr : Loc) :
    Persistent (proxySharedDef (GF := GF) γ c k pr) := by
  unfold proxySharedDef; infer_instance

/-- The main loop's state (`ownQ`, `OwnProp.lean`), for some ghost name of its pending slots. -/
def proxyOwnDef (γ : QNames) (c : QConf) (k : Nat) (pr : Loc) : IProp GF :=
  iprop(∃ γq : GName, ownQ γ c k pr γq)

end defs

end Perennial.raxos

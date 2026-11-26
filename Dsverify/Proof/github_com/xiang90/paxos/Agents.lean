/-
Ported from dsverify-lab examples/paxos/proof/Paxos/Proof/Agents.lean (lab master 7a84fb35; notes/dsv-paxos.md).

The agents' API (stage 1 interface, frozen at `stage1-frozen`): what the deployment
(`netcluster.go`) needs of the acceptor, the learner and the proposer: their constructors and
their main loops, over the transport (`Net.lean`) with `msgOK Γ` as the message predicate and the
Paxos hub (`Inv.lean`).

Each agent's representation (`own_acceptor`, `own_learner`, `own_proposer`) is its module's
slot: the deployment only passes it from the constructor to the loop, never unfolds it.
-/
module

public import Dsverify.Proof.github_com.xiang90.paxos.Inv

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net

namespace github_com.xiang90.paxos

attribute [local instance] GooseGlobalGS.gooseInvGS

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [π : NetProtoGS]

/-- The `network` interface value of agent network `nt`. -/
abbrev ntIface (nt : Loc) : GoInterface := interface.mkOk (go.GoType.PointerType tcpNetwork.ty) #nt

/-- Where an agent runs: the protocol, its node and its network. -/
def agentEnv (Γ : Names) (nt nd : Loc) (amap : GMap w64 GoString) (ids : List w64) (id : w64) :
    IProp GF :=
  iprop(isPaxos Γ ∗ is_node nd (msgOK Γ) amap ids ∗ own_net nt (msgOK Γ) nd id ∗ ⌜id ∈ ids⌝)

/-- Acceptor `id` at `ap` (the acceptor module's slot). -/
def own_acceptor (Γ : Names) (ap : Loc) (id : w64) : IProp GF :=
  iprop(∃ (nt nd : Loc) (amap : GMap w64 GoString) (ids : List w64) (lsl : GoSlice) (s : AccState)
      (acc : message) (prom : GoInterface),
    agentEnv Γ nt nd amap ids id ∗ ⌜id ∈ accIds⌝ ∗ stOwn Γ id s ∗
    ap.[acceptor, go!"id"] ↦ id ∗ ap.[acceptor, go!"learners"] ↦ lsl ∗ lsl ↦*□ lrnIds ∗
    ap.[acceptor, go!"accept"] ↦ acc ∗ ap.[acceptor, go!"promised"] ↦ prom ∗
    ap.[acceptor, go!"nt"] ↦ (ntIface nt) ∗
    ⌜acc.n' = s.k ∧ acc.value' = s.w ∧ msgWf acc ∧
      ∃ pm : message, prom = interface.mkOk message.ty #pm ∧ pm.n' = s.p⌝)

/-- A learner's view of acceptor `a`: the latest `Accept` it took from `a` (number 0: none). -/
def lrnEntry (Γ : Names) (a : w64) (x : GoInterface) : IProp GF :=
  iprop(∃ m : message, ⌜x = interface.mkOk message.ty #m ∧ m.typ' = W64 4 ∧ msgWf m⌝ ∗
    (⌜m.n' = W64 0⌝ ∨ (⌜m.from' = a⌝ ∗ accW Γ a m.n' m.value')))

/-- Learner `id` at `lp` (the learner module's slot). -/
def own_learner (Γ : Names) (lp : Loc) (id : w64) : IProp GF :=
  iprop(∃ (nt nd : Loc) (amap : GMap w64 GoString) (ids : List w64) (am : Loc)
      (M : GMap w64 GoInterface),
    agentEnv Γ nt nd amap ids id ∗ ⌜id ∈ lrnIds⌝ ∗
    lp.[learner, go!"id"] ↦ id ∗ lp.[learner, go!"acceptors"] ↦ am ∗
    lp.[learner, go!"nt"] ↦ (ntIface nt) ∗ am ↦$ M ∗
    ⌜∀ a, (M !! a).isSome ↔ a ∈ accIds⌝ ∗ [∗map] a ↦ x ∈ M, lrnEntry Γ a x)

/-- Proposer `id` at `pp`, proposing `v`, as `newProposer` makes it (the proposer module's
slot): no round yet, no promise. -/
def own_proposer (Γ : Names) (pp : Loc) (id : w64) (v : GoString) : IProp GF :=
  iprop(∃ (nt nd : Loc) (amap : GMap w64 GoString) (ids : List w64) (am : Loc),
    agentEnv Γ nt nd amap ids id ∗ ⌜id ∈ propIds ∧ (v.length : Int) < 2 ^ 48⌝ ∗
    pp.[proposer, go!"id"] ↦ id ∗ pp.[proposer, go!"lastSeq"] ↦ W64 0 ∗
    pp.[proposer, go!"value"] ↦ v ∗ pp.[proposer, go!"valueN"] ↦ W64 0 ∗
    pp.[proposer, go!"acceptors"] ↦ am ∗ pp.[proposer, go!"nt"] ↦ (ntIface nt) ∗
    am ↦$ (({[W64 1 := interface.mkOk message.ty #(zero_val message)]} ∪
      {[W64 2 := interface.mkOk message.ty #(zero_val message)]} ∪
      {[W64 3 := interface.mkOk message.ty #(zero_val message)]}) : GMap w64 GoInterface))

end defs

section specs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [π : NetProtoGS]
variable [package_sem : paxos.Assumptions]

local notation "pkg" => pkg_id.github_com.xiang90.paxos

/-- `newAcceptor(id, nt, learners...)`, for acceptor `id` at its initial state. -/
abbrev newAcceptor.spec : Prop :=
  ∀ (Γ : Names) (id : w64) (nt nd : Loc) (amap : GMap w64 GoString) (ids : List w64)
    (lsl : GoSlice),
  id ∈ accIds →
  {{ isPkgInit (PROP := IProp GF) pkg ∗ agentEnv Γ nt nd amap ids id ∗
      stOwn Γ id AccState.init ∗ lsl ↦*□ lrnIds }}
    (App (App (App (Val (@! newAcceptor)) (Val #id)) (Val #(ntIface nt))) (Val #lsl))
  {{ (ap : Loc), RET #ap; own_acceptor Γ ap id }}

/-- `a.run()`: never returns. -/
abbrev acceptor.run.spec : Prop :=
  ∀ (Γ : Names) (ap : Loc) (id : w64),
  {{ isPkgInit (PROP := IProp GF) pkg ∗ own_acceptor Γ ap id }}
    (App (Val (ap @!! go.GoType.PointerType acceptor.ty @!! go!"run")) (Val #()))
  {{ RET #(); False }}

/-- `newLearner(id, nt, acceptors...)`, for a learner of the three acceptors. -/
abbrev newLearner.spec : Prop :=
  ∀ (Γ : Names) (id : w64) (nt nd : Loc) (amap : GMap w64 GoString) (ids : List w64)
    (asl : GoSlice),
  id ∈ lrnIds →
  {{ isPkgInit (PROP := IProp GF) pkg ∗ agentEnv Γ nt nd amap ids id ∗ asl ↦*□ accIds }}
    (App (App (App (Val (@! newLearner)) (Val #id)) (Val #(ntIface nt))) (Val #asl))
  {{ (lp : Loc), RET #lp; own_learner Γ lp id }}

/-- `l.learn()`: a chosen value. -/
abbrev learner.learn.spec : Prop :=
  ∀ (Γ : Names) (lp : Loc) (id : w64),
  {{ isPkgInit (PROP := IProp GF) pkg ∗ own_learner Γ lp id }}
    (App (Val (lp @!! go.GoType.PointerType learner.ty @!! go!"learn")) (Val #()))
  {{ (v : GoString), RET #v; own_learner Γ lp id ∗ chosenW Γ v ∗ ⌜(v.length : Int) < 2 ^ 48⌝ }}

/-- `newProposer(id, v, nt, acceptors...)`, for proposer `id` with the input `v`. -/
abbrev newProposer.spec : Prop :=
  ∀ (Γ : Names) (id : w64) (v : GoString) (nt nd : Loc) (amap : GMap w64 GoString)
    (ids : List w64) (asl : GoSlice),
  id ∈ propIds → (v.length : Int) < 2 ^ 48 →
  {{ isPkgInit (PROP := IProp GF) pkg ∗ agentEnv Γ nt nd amap ids id ∗ asl ↦*□ accIds }}
    (App (App (App (App (Val (@! newProposer)) (Val #id)) (Val #v)) (Val #(ntIface nt)))
      (Val #asl))
  {{ (pp : Loc), RET #pp; own_proposer Γ pp id v }}

/-- `p.run()`: the proposer's one proposal (its token), of a registered input. -/
abbrev proposer.run.spec : Prop :=
  ∀ (Γ : Names) (pp : Loc) (id : w64) (v : GoString) (c : w64),
  {{ isPkgInit (PROP := IProp GF) pkg ∗ own_proposer Γ pp id v ∗ ptok Γ id ∗ regW Γ c v }}
    (App (Val (pp @!! go.GoType.PointerType proposer.ty @!! go!"run")) (Val #()))
  {{ RET #(); True }}

end specs

end github_com.xiang90.paxos

end Perennial

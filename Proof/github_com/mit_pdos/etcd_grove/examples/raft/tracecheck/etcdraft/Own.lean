/-
Lean-first (no Rocq counterpart).

# The search's copy-on-write: owned copies (Probe, 2026-11-08)

The checker's search never writes a state it was handed: an action `clone`s the state (a new
struct and a new server map sharing the servers) and `mut`s the server it changes (a `copy`: a
new struct and a new `MatchIndex` map), writes the copies, and returns the clone, which nobody
writes again. So a state or a server is read-only (`stateRO`, `serverRO`, `Rep.lean`) except
while the action building it holds it: `serverOwn` is a server copy being written, persisted into
`serverRO` once done (`serverOwn_persist`). Layer C's Probe (`notes/trace-validation-plan.md`,
"Probe set") checks this design on `(*State).Timeout`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Rep

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace Etcdraft

open Iris Iris.BI Iris.ProofMode

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Assumptions]

/-- A `*Server` copy being written: `serverRO`'s, with the struct and the `MatchIndex` map owned. -/
def serverOwn (p : Loc) (v : Server) : IProp GF :=
  iprop(∃ (g : G.Server) (mm : GMap w64 w64), p ↦ g ∗
    ⌜sint.Z g.CurrentTerm' = v.currentTerm ∧ g.State' = stringToGoString v.state ∧
      uint.nat g.VotedFor' = v.votedFor ∧ sint.Z g.CommitIndex' = v.commitIndex ∧
      sint.Z g.PendingConfChangeIndex' = v.pendingConfChangeIndex⌝ ∗
    logRO g.Log' v.log ∗ setRO g.VotesResponded' v.votesResponded ∗
    setRO g.VotesGranted' v.votesGranted ∗
    g.MatchIndex' ↦$ mm ∗
    ⌜∀ j : w64, sint.Z ((mm !! j).getD (W64 0)) = v.matchIndex (uint.nat j)⌝ ∗
    configRO g.Config' v.config ∗ durableRO g.Durable' v.durable)

/-- A written copy, frozen. -/
theorem serverOwn_persist (p : Loc) (v : Server) :
    serverOwn (GF := GF) p v ⊢ |==> serverRO p v := by
  iintro H
  iunfold serverOwn at H
  icases H with ⟨%g, %mm, Hp, %Hf, #Hl, #Hr, #Hg, Hm, %Hmi, #Hc, #Hd⟩
  ipersist Hp
  ipersist Hm
  imodintro
  iunfold serverRO
  iexists g, mm
  iframe Hp Hl Hr Hg Hm Hc Hd
  ipureintro; exact ⟨Hf, Hmi⟩

end defs

end Etcdraft
end EtcdGrove
end Perennial

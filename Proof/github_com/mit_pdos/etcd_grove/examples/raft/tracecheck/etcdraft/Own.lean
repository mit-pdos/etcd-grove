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

/-- A `*State` clone being built: the struct and the server map owned; the servers in `M` are
copies being written (`serverOwn`), the others shared (`serverRO`). -/
def stateOwn (p : Loc) (st : State) (M : List ID) : IProp GF :=
  iprop(∃ (g : G.State) (sm : GMap w64 Loc), p ↦ g ∗ setRO g.Server' st.server ∗
    g.S' ↦$ sm ∗
    ⌜∀ k : w64, (sm !! k).isSome ↔ uint.nat k ∈ st.server⌝ ∗
    ([∗list] i ∈ st.server, ∃ q : Loc, ⌜sm !! (W64 (Int.ofNat i)) = some q⌝ ∗
      (if i ∈ M then serverOwn q (st.s i) else serverRO q (st.s i))) ∗
    bagRO g.Messages' st.messages ∗ bagRO g.PendingMessages' st.pendingMessages ∗
    ⌜sint.Z g.ReconfigCount' = st.reconfigCount⌝)

/-- A built clone, frozen. -/
theorem stateOwn_persist (p : Loc) (st : State) (M : List ID) :
    stateOwn (GF := GF) p st M ⊢ |==> stateRO p st := by
  iintro H
  iunfold stateOwn at H
  icases H with ⟨%g, %sm, Hp, #Hsrv, Hm, %Hkeys, Hsrvs, #Hb1, #Hb2, %Hrc⟩
  ipersist Hp
  ipersist Hm
  ihave Hsrvs : iprop([∗list] i ∈ st.server, |==> ∃ q : Loc, ⌜sm !! (W64 (Int.ofNat i)) = some q⌝ ∗
      serverRO (GF := GF) q (st.s i)) $$ [Hsrvs]
  · iapply (BigSepL.bigSepL_mono (fun {_ i} _ => ?_)) $$ Hsrvs
    iintro ⟨%q, %Hq, Hs⟩
    by_cases hi : i ∈ M
    · simp only [hi, ite_true]
      imod serverOwn_persist $$ Hs with Hs
      imodintro; iexists q; iframe Hs; ipureintro; exact Hq
    · simp only [hi, ite_false]
      imodintro; iexists q; iframe Hs; ipureintro; exact Hq
  imod BigSepL.bigSepL_bupd _ _ $$ Hsrvs with Hsrvs
  imodintro
  iunfold stateRO
  iexists g, sm
  iframe Hp Hsrv Hm Hb1 Hb2 Hsrvs
  ipureintro; exact ⟨Hkeys, Hrc⟩

end defs

end Etcdraft
end EtcdGrove
end Perennial

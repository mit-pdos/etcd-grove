/-
**The restart construction's sub-facts** (restart S6 B2, 2026-11-14): the lemmas `NewServer.wp_proofR`
(`NewServerR.lean`) uses that no other proof provides yet, each stated here so that the main proof
stays a copy of `NewServer.wp_proofG`'s with the boot steps replaced. Lean-first.

STATUS: being written; the lemmas marked `sorry` are open (the handoff's list,
`notes/restart-s56-handoff.md`, "B2 proof").
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.BuiltRestart

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- The restarted names' compaction revision of a log is the stopped one's. -/
theorem restartNames_crevOf {ρ ρ' : ReqNames} (h : restartNames ρ ρ') (A : List EntryModel) :
    crevOf ρ'.rd.kv A = crevOf ρ.rd.kv A := by
  obtain ⟨-, h2, h3, -⟩ := h.2.1
  unfold crevOf; rw [h2, h3]

/-- (Probe P5; the restart contract's clause (G)) **The members' peer URLs at a committed log are the
boot log's**: no committed conf change adds a member (every `AddNode` names a present id) and the
attribute updates keep peer URLs (`withAttrs`). OPEN: the phase-2 invariant of `RestConf.lean`
(the `members` bucket exactly the encodings of `r.mem`, peer URLs `memBoot`'s). -/
theorem restart_peerURLs (γ : ServerRaftNames) (γk : KVNames) (A : List EntryModel)
    (hpre : γ.pre = []) :
    ⊢ kvInv (GF := GF) γ γk -∗ srvRaftLogInv γ -∗ srvRLogLb γ A ={⊤}=∗
      ⌜∀ f, ((restModel (W64 0) γ.raft.boot A).mem.lookup f).map apply.MemberM.peerURLs =
        ((memBoot γ.raft.boot).lookup f).map apply.MemberM.peerURLs⌝ := by
  sorry

end lemmas

end EtcdGrove
end Perennial

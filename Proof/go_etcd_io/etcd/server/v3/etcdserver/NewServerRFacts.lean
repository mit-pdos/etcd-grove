/-
**The restart construction's sub-facts** (restart S6 B2, 2026-11-14): the lemmas `NewServer.wp_proofR`
(`NewServerR.lean`) uses that no other proof provides yet, each stated here so that the main proof
stays a copy of `NewServer.wp_proofG`'s with the boot steps replaced. Lean-first.

STATUS: being written; the lemmas marked `sorry` are open (the handoff's list,
`notes/restart-s56-handoff.md`, "B2 proof").
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.BuiltRestart
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ImageLeases

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

/-- The leased rest image reads only the KV names' start values (`c0`, `ch0`): the restarted names'
is the stopped one's. -/
theorem restartNames_bkRestAtL {ρ ρ' : ReqNames} (h : restartNames ρ ρ') (b : List EntryM)
    (L : List EntryModel) (D : backend.Data) :
    bkRestAtL ρ'.rd.kv b L D ↔ bkRestAtL ρ.rd.kv b L D := by
  obtain ⟨-, h2, h3, -⟩ := h.2.1
  unfold bkRestAtL kvLeases; rw [h2, h3]

/-- (The restarted lessor's requested TTLs) **`tableReq` of a table is at most the records' TTLs**,
for records whose ids are the table's (`imageLeasesAt_recs`'s facts): `NewLessor.spec`'s premise at
`reqOf := tableReq T`. -/
theorem tableReq_le_recs (T : LeaseTable) (recs : List (w64 × w64 × w64)) (hn : T.ids.Nodup)
    (hperm : (recs.map (·.1)).Perm T.ids)
    (hge : ∀ x ∈ recs, ∀ p ∈ T, p.1 = x.1 → sint.Z p.2 ≤ sint.Z x.2.1) :
    ∀ x ∈ recs, sint.Z (tableReq T x.1) ≤ sint.Z x.2.1 := by
  intro x hx
  have hm : x.1 ∈ T.ids := hperm.subset (List.mem_map.2 ⟨x, hx, rfl⟩)
  obtain ⟨p, hp, hp1⟩ := List.mem_map.1 hm
  rw [← hp1, tableReq_of_mem hn hp]
  exact hge x hx p hp hp1

/-- (The restarted lessor's guard) **A cluster that grants no lease has an empty applied table**:
the image's lease bucket holds no record unless `lg`. OPEN (from the KV invariant: with
`lg = false` no committed `LeaseGrant` takes effect). -/
theorem restart_noGrant (γr : ReadNames) (A : List EntryModel) (hpre : γr.raft.pre = []) :
    ⊢ kvInv (GF := GF) γr.raft γr.kv -∗ srvRaftLogInv γr.raft -∗ srvRLogLb γr.raft A ={⊤}=∗
      ⌜γr.kv.lg = false → (appliedTable γr A).ids = []⌝ := by
  sorry

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

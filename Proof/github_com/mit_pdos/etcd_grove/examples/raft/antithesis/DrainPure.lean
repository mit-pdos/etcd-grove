/-
Lean-first (no Rocq counterpart). #33 S4: **the pure steps of `Cluster.drain`'s loop**
(`Cluster__drain.lean`), between raft's `HasReady`/`Ready` posts and the Sim's relations:
- a loop head has nothing of a `Ready` left to report (`reach_ce`, with `AntSim.reach_pend`);
- `HasReady` false ends the drain (`noReady_of`): the node idle at the view's hard state, role and
  log (`PIdle` against `RsView`), so `Quiet.noReady` moves the view to the node's state, which is
  `nodeOwn`'s `drained` phase;
- the Go's report condition (`write || role != n.role`, with `write = hsNew || len(Entries) > 0`)
  is `AntSim.Reported` (`goReport_iff`), given raft's `Ready` hands out a hard state only when it
  differs from the last one (`hne`: raft's `!isHardStateEqual(hardSt, prevHardSt)`, not yet in the
  `Ready` form);
- a `Ready` with no entries is `ReadyOutP` without log matching (`readyOutP_noEnts`: the log is the
  view's).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.DrainReports

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntHarness

open Iris go_etcd_io.raft.v3

section pure
variable [GooseExts]

/-- A loop head has no committed entries left to report. -/
theorem reach_ce {id : w64} {net : List Msg} {v : AntSim.NodeView} {ps₁ : PState}
    (hr : AntSim.Reach id net v ps₁) : v.ce = [] := by
  cases hr with
  | stay hi => exact hi.2.2
  | input _ _ hi _ _ _ _ => exact hi.2.2
  | advance _ _ hc _ _ => exact hc

theorem roleGo_inj {r r' : Role} (h : roleGo r = roleGo r') : r = r' := by
  cases r <;> cases r' <;> first | rfl | (simp [roleGo, StateFollower, StateCandidate, StateLeader] at h)

theorem roleStr_roleGo_inj {r r' : Role} (h : roleStr (roleGo r) = roleStr (roleGo r')) : r = r' := by
  cases r <;> cases r' <;> first | rfl | (simp [roleStr, roleGo, StateFollower, StateCandidate,
    StateLeader, StatePreCandidate] at h)

theorem hardStateM_mk_inj {a b c a' b' c' : w64}
    (h : HardStateM.mk a b c = HardStateM.mk a' b' c') : a = a' ∧ b = b' ∧ c = c' := by
  cases h; exact ⟨rfl, rfl, rfl⟩

/-- **`HasReady` false at a loop head**: the view moves to the node's state with nothing queued
(`Quiet.noReady`), which is idle, and the record agrees with it; its hard state, role and log are
the view's. -/
theorem noReady_of {id : w64} {net : List Msg} {v : AntSim.NodeView} {ps₁ : PState} {rs : RNState}
    (hr : AntSim.Reach id net v ps₁) (hP : PIdle rs ps₁) (hRs : RsView rs v) :
    AntSim.Quiet id net v { v with ps := ps₁, qs := [] } ∧
      ({ v with ps := ps₁, qs := [] } : AntSim.NodeView).Idle ∧
      RsView rs { v with ps := ps₁, qs := [] } ∧
      ps₁.term = v.ps.term ∧ ps₁.vote = v.ps.vote ∧ ps₁.commit = v.ps.commit ∧
      ps₁.role = v.ps.role ∧ ps₁.log = v.ps.log := by
  obtain ⟨hob, hhs, hro, hlog⟩ := hP
  obtain ⟨hphs, hrole, hents, hdel, hst, hun, hflw⟩ := hRs
  obtain ⟨ht, hv, hc⟩ := hardStateM_mk_inj (hhs.trans hphs)
  have hr' : ps₁.role = v.ps.role := roleGo_inj (hro.trans hrole)
  have hl : ps₁.log = v.ps.log := hlog.symm.trans hents
  have hpe : v.pend = [] := AntSim.reach_pend hr
  have hce : v.ce = [] := reach_ce hr
  refine ⟨.noReady v ps₁ hr hob ht hv hc hr' hl, ⟨rfl, hpe, hce⟩,
    ⟨?_, ?_, ?_, hdel, hst, hun, hflw⟩, ht, hv, hc, hr', hl⟩
  · simp only; rw [ht, hv, hc]; exact hphs
  · simp only; rw [hr']; exact hrole
  · simp only; rw [hl]; exact hents

/-- `Ready`'s hard state is new (`hsNew`: non-nil and not empty). -/
def HsNew (h : HardStateM) : Prop := ¬ (h.Term' = W64 0 ∧ h.Vote' = W64 0 ∧ h.Commit' = W64 0)

instance (h : HardStateM) : Decidable (HsNew h) := by unfold HsNew; infer_instance

/-- **The Go's report condition is `Reported`**: `write || role != n.role` (`write = hsNew ||
len(rd.Entries) > 0`; the role the `SoftState`'s, or the last reported one), at a `Ready` whose role
and hard state after it are the node's (`ReadyOut`), from a record whose last reported ones are the
view's (`RsView`), when a hard state is handed out only if it differs from the last (`hne`). -/
theorem goReport_iff {v : AntSim.NodeView} {rs : RNState} {ps₁ : PState} {h : HardStateM}
    {es : List EntryM} {ss : Option (w64 × StateType)} (msgs qs : List Msg) (ce : List EntryM)
    (hphs : rs.phs = HardStateM.mk v.ps.term v.ps.vote v.ps.commit)
    (hrole : rs.role = roleGo v.ps.role)
    (hra : roleAfter rs.role ss = roleGo ps₁.role)
    (hnext : phsNext rs.phs h = HardStateM.mk ps₁.term ps₁.vote ps₁.commit)
    (hne : HsNew h → h ≠ rs.phs) :
    (HsNew h ∨ es ≠ [] ∨ roleStr (roleAfter rs.role ss) ≠ roleStr rs.role) ↔
      AntSim.Reported v (readyDOf ps₁ es msgs qs ce) := by
  unfold AntSim.Reported readyDOf
  simp only
  rw [hra, hrole]
  have hrs : roleStr (roleGo ps₁.role) ≠ roleStr (roleGo v.ps.role) ↔ ps₁.role ≠ v.ps.role :=
    ⟨fun h1 h2 => h1 (by rw [h2]), fun h1 h2 => h1 (roleStr_roleGo_inj h2)⟩
  rw [hrs]
  have hhs : HsNew h ↔ (ps₁.term ≠ v.ps.term ∨ ps₁.vote ≠ v.ps.vote ∨ ps₁.commit ≠ v.ps.commit) := by
    constructor
    · intro hn
      have h2 := hne hn
      rw [phsNext_ne _ _ hn] at hnext
      rw [hnext, hphs] at h2
      apply Classical.byContradiction
      intro hc
      simp only [not_or, ne_eq, Classical.not_not] at hc
      apply h2
      rw [hc.1, hc.2.1, hc.2.2]
    · intro hd hn
      rw [phsNext_empty _ _ hn, hphs] at hnext
      obtain ⟨a, b, c⟩ := hardStateM_mk_inj hnext
      rcases hd with hd | hd | hd
      · exact hd a.symm
      · exact hd b.symm
      · exact hd c.symm
  rw [hhs]
  simp only [or_assoc]

/-- **A `Ready` with no entries at the protocol level** (`ReadyOutP`, `readyOutP_of` with its log
matching discharged: the node's log is the view's). -/
theorem readyOutP_noEnts {id : w64} {v : AntSim.NodeView} {rs : RNState} {ps : PState}
    {h : HardStateM} {ce : List EntryM} {ms : List QMsg} {ss : Option (w64 × StateType)}
    {L : Option SnapLoan} {qs : List Msg} {ip : Nat}
    (hRs : RsView rs v) (hce : v.ce = []) (hip : ip = lcpLen v.ps.log ps.log)
    (hout : ReadyOut id rs ps h [] ce ms ss L)
    (hqs : qs.Perm (ps.outbox.filter (fun m => decide (m.dst = id))))
    (hbase : ps.base = base0) (hidx : AntSim.LogIdx ps.log)
    (hvot : ∀ q ∈ ms.filterMap (fun q => absMsgOf q.st), ∃ j : Fin 3, q.dst = AntSim.nodeId j) :
    AntSim.ReadyOutP id v ps (readyDOf ps [] (ms.filterMap (fun q => absMsgOf q.st)) qs ce) := by
  have hlog : ps.log = v.ps.log := by
    rw [← hout.2.2.1, ← hRs.2.2.1, hout.2.2.2.2.2.2.2.2]
    simp [readyDurable, RaftState.next, appendEnts]
  refine readyOutP_of hRs hce hip hout (fun _ h => by cases h) hqs hbase hidx ?_ hvot
  intro k e f he hf _
  rw [hlog, he] at hf
  exact Option.some.inj hf

end pure

end AntHarness
end EtcdGrove
end Perennial

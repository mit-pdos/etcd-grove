/-
Lean-first (no Rocq counterpart).

# Parity B2: from the B2 relation to the B1 one in a run with the B2 modes off

`AntSimD` is `AntSim` with conjuncts guarded by the B2 modes or restated over `EffTerm` and the undo
record, plus the B2 bookkeeping. In a run with the B2 modes off (`SyncB1`), `AntSimD` gives `AntSim`
(`antSimD_toB1`): sync, the disk is raft's state, which `LeaderConfOkD` reads. The converse is not a projection: `AntSimD`'s
`EffTerm` forms keep the binding's facts for the terms between a node's undo record and its term,
which `AntSim` does not say (round 2: each B1 kind restated over `AntSimD`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.StmtsB2
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.GC
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.LiftC
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.BindM

@[expose] public section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace AntSim

open GMap go_etcd_io.raft.v3

section b1carry
variable [GooseExts]

/-- The B2 modes are off: sync storage, no batching, `-parallel` or split writes. -/
def SyncB1 (R : RunCfg) : Prop :=
  R.md.async = false ∧ R.drv.batch = false ∧ R.drv.split = 0 ∧ R.drv.parallel = false

theorem AckInD.toAckIn {N : Nat} {S : AntCheck.State} {i : Fin N} {dst : AntCheck.Str} {t k : Int}
    (h : AckInD S i dst t k) : AckIn S (nameOf (nodeId i)) dst t k := by
  obtain ⟨a, ha, h1, h2, h3, h4, h5, -⟩ := h
  exact ⟨a, ha, h1, h2, h3, h4, h5⟩

theorem AckInX.toAckIn {N : Nat} {S : AntCheck.State} {n j : Fin N} {t k : Int}
    (h : AckInX S n j t k) : AckIn S (nameOf (nodeId j)) (nameOf (nodeId n)) t k := by
  obtain ⟨a, ha, h1, h2, h3, h4, h5, -⟩ := h
  exact ⟨a, ha, h1, h2, h3, h4, h5⟩

/-- `LeaderPartD`'s acknowledgements are `LeaderPart`'s. -/
theorem leaderPartD_acks {N : Nat} {S : AntCheck.State} {n : Fin N} {v : NodeView}
    (h3 : ∀ (j : Fin N) (k : w64), uint.Z k ≤ uint.Z (matchOf v.ps (nodeId j)) →
      plogTermAt v.ps.base v.ps.log k = some v.ps.term → AckInX S n j (uint.Z v.ps.term) (uint.Z k))
    (h4 : ∀ j : Fin N, j ≠ n → matchOf v.ps (nodeId j) = W64 0 ∨
      AckInX S n j (uint.Z v.ps.term) (uint.Z (matchOf v.ps (nodeId j)))) :
    (∀ (j : Fin N) (k : w64), uint.Z k ≤ uint.Z (matchOf v.ps (nodeId j)) →
      plogTermAt v.ps.base v.ps.log k = some v.ps.term →
      AckIn S (nameOf (nodeId j)) (nameOf (nodeId n)) (uint.Z v.ps.term) (uint.Z k)) ∧
    (∀ j : Fin N, j ≠ n → matchOf v.ps (nodeId j) = W64 0 ∨
      AckIn S (nameOf (nodeId j)) (nameOf (nodeId n)) (uint.Z v.ps.term)
        (uint.Z (matchOf v.ps (nodeId j)))) :=
  ⟨fun j k hk ht => (h3 j k hk ht).toAckIn, fun j hj => (h4 j hj).imp_right AckInX.toAckIn⟩

/-- `NetOkD`'s receipt facts for a message give `NetOk`'s. -/
theorem netRcD_toB1 {N : Nat} {S : AntCheck.State} {m : Msg} {i : Fin N} (hi : m.src = nodeId i)
    (h : ((m.ty = .app ∨ m.ty = .heartbeat) →
          (AntCheck.toAppendFact (msgOf m m.dst) >>= S.sendable) = .ok true) ∧
        (m.ty = .vote → ∃ f, AntCheck.voteFact (msgOf m m.dst) = .ok f ∧ f ∈ S.msgs) ∧
        ((m.ty = .voteResp ∧ m.reject = false) →
          ({ type := go!"grant", src := nameOf m.src, dst := nameOf m.dst, term := uint.Z m.term } :
            AntCheck.Fact) ∈ S.msgs) ∧
        ((m.ty = .appResp ∧ m.reject = false ∧ m.index ≠ W64 0) → ∀ i : Fin N, m.src = nodeId i →
          AckInD S i (nameOf m.dst) (uint.Z m.term) (uint.Z m.index))) :
    ((m.ty = .app ∨ m.ty = .heartbeat) →
          (AntCheck.toAppendFact (msgOf m m.dst) >>= S.sendable) = .ok true) ∧
        (m.ty = .vote → ∃ f, AntCheck.voteFact (msgOf m m.dst) = .ok f ∧ f ∈ S.msgs) ∧
        ((m.ty = .voteResp ∧ m.reject = false) →
          ({ type := go!"grant", src := nameOf m.src, dst := nameOf m.dst, term := uint.Z m.term } :
            AntCheck.Fact) ∈ S.msgs) ∧
        ((m.ty = .appResp ∧ m.reject = false ∧ m.index ≠ W64 0) →
          AckIn S (nameOf m.src) (nameOf m.dst) (uint.Z m.term) (uint.Z m.index)) :=
  ⟨h.1, h.2.1, h.2.2.1, fun ht => by rw [hi]; exact (h.2.2.2 ht i hi).toAckIn⟩

/-- `NetOkD` gives `NetOk` (sync) given the disk form of the leaders' commits on their messages. -/
theorem netOkD_toB1 {R : RunCfg} {S : AntCheck.State} {net : List Msg} (hs : R.md.async = false)
    (h : NetOkD R S net) (hlc : LeadCommitMsgOk R.N S net) : NetOk R S net := by
  obtain ⟨h1, hhb, h3, -, h5, h6, h7⟩ := h
  refine ⟨fun m hm => ?_, fun m hm hty j hj hle => (hhb m hm hty j hj).1 hle, h3, hlc, h5, h6, h7⟩
  obtain ⟨hty, ⟨i, hi, -, hti⟩, j, hj, hrc⟩ := h1 m hm
  exact ⟨hty, ⟨i, hi, hti hs⟩, j, hj,
    fun hle => netRcD_toB1 hi (hrc (Int.le_trans (effTerm_le S j.val) hle))⟩

/-- `NetOkD` gives `NetOk` (sync) at the state with the commits raised to the in-memory ones. -/
theorem netOkD_toB1L {R : RunCfg} {S : AntCheck.State} {net : List Msg} (hs : R.md.async = false)
    (hlen : S.commitIndex.length = R.N) (h : NetOkD R S net) : NetOk R (liftC S) net := by
  obtain ⟨h1, hhb, h3, h4, h5, h6, h7⟩ := h
  refine ⟨fun m hm => ?_, fun m hm hty j hj hle => ?_, h3, fun m hm hty i hi hro hct => ?_, h5, h6, h7⟩
  · obtain ⟨hty, ⟨i, hi, -, hti⟩, j, hj, hrc⟩ := h1 m hm
    exact ⟨hty, ⟨i, hi, hti hs⟩, j, hj,
    fun hle => netRcD_toB1 hi (hrc (Int.le_trans (effTerm_le S j.val) hle))⟩
  · rcases (hhb m hm hty j hj).1 hle with h | h
    · exact .inl h
    · exact .inr (Int.le_trans h (le_liftC S j.val))
  · obtain ⟨c, hc, hle⟩ := h4 m hm hty i hi hro hct
    rw [liftC_get S (by rw [hlen]; exact i.isLt), hc]
    exact Int.le_trans hle (Int.le_max_right _ _)

/-- A node part does not read the other nodes' commits. -/
theorem nodeOk_liftC {R : RunCfg} {dec : CCDec} {S : AntCheck.State} {net : List Msg} {n : Fin R.N}
    {v : NodeView} (hq : S.queue[n.val]! = []) (h : NodeOk R dec S net n v) :
    NodeOk R dec (liftC S) net n v := by
  obtain ⟨⟨a, b, c, d⟩, rest⟩ := h
  exact ⟨⟨a, b, c, by rw [liftC_nil hq]; exact d⟩, rest⟩

theorem nodeOk_unliftC {R : RunCfg} {dec : CCDec} {S : AntCheck.State} {net : List Msg} {n : Fin R.N}
    {v : NodeView} (hq : S.queue[n.val]! = []) (h : NodeOk R dec (liftC S) net n v) :
    NodeOk R dec S net n v := by
  obtain ⟨⟨a, b, c, d⟩, rest⟩ := h
  exact ⟨⟨a, b, c, by rw [← liftC_nil hq]; exact d⟩, rest⟩

theorem xnetOkD_toB1 {R : RunCfg} {S : AntCheck.State} {xnet : List XMsg} (h : XNetOkD R S xnet) :
    XNetOk R S xnet := by
  intro x hx
  obtain ⟨i, hi⟩ := h x hx
  exact ⟨i, Int.le_trans hi (effTerm_le S i.val)⟩

theorem nodeFactsD_toB1 {R : RunCfg} {n : Fin R.N} {v : NodeView} (hs : SyncB1 R)
    (hm : v.mems = []) (hp : v.parts = [])
    (h : NodeFactsD R n v) : NodeFacts R n v := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  have h6' := h6 hs.1
  rw [hm, hp] at h6'
  exact ⟨h1 hs.2.1, h2, h3, h4, h5, h6', h7⟩

theorem nodeOkD_toB1 {R : RunCfg} {dec : CCDec} {S : AntCheck.State} {net : List Msg} {n : Fin R.N}
    {v : NodeView} (hs : SyncB1 R) (hpa : v.parts = [])
    (h : NodeOkD R dec S net n v) : NodeOk R dec S net n v := by
  obtain ⟨hd, hm, hsy, hu, hq, hr, hcl, hf, hl, hc, hp, -, hx, hqs, ht, hca, hxc, hlo, hvs, -⟩ := h
  have hdur : v.dur = durOf v.r := (hsy hs.1 hs.2.1 hs.2.2.1 hs.2.2.2).2.1
  have hme : v.mems = [] := (hsy hs.1 hs.2.1 hs.2.2.1 hs.2.2.2).1
  refine ⟨hd, hm, hsy, hu, hq, hr, hcl, nodeFactsD_toB1 hs hme hpa hf, fun hrl => ?_, fun hrc => ?_,
    hp hs.2.1, hx, fun q hq' => ?_, ht, hca, hxc, hlo, hvs⟩
  · obtain ⟨l1, l2, l3, l4, l5⟩ := hl hrl
    obtain ⟨l3, l4⟩ := leaderPartD_acks l3 l4
    refine ⟨l1, l2, l3, l4, ?_⟩
    have hlog : v.dur.log = v.r.full := by rw [hdur]; rfl
    obtain ⟨c1, c2⟩ := l5 (.inl hlog)
    exact ⟨c1, by rw [← hlog]; exact c2⟩
  · obtain ⟨c1, c2⟩ := hc hrc
    exact ⟨c1, c2 (by rw [hdur]; rfl)⟩
  · rcases hqs q hq' with h | h
    · exact h
    · exact absurd hme h.2.2.2.2.2.2.1

/-- **`AntSimD` gives `AntSim`** in a run with the B2 modes off. -/
theorem antSimD_toB1 {R : RunCfg} {dec : CCDec} {S : AntCheck.State} {V : Fin R.N → NodeView}
    {net : List Msg} {xnet : List XMsg} (hs : SyncB1 R) (hpa : ∀ n, (V n).parts = [])
    (h : AntSimD R dec S V net xnet) : AntSim R dec S V net xnet := by
  obtain ⟨hsh, hb, hn, hx, hv⟩ := h
  have hq : ∀ i : Fin R.N, S.queue[i.val]! = [] := fun i => by
    have hqi : QueueIs S i (V i) := (hv i).2.2.2.2.1
    have hm := ((hv i).2.2.1 hs.1 hs.2.1 hs.2.2.1 hs.2.2.2).1
    unfold QueueIs at hqi; rw [hqi, hm]; rfl
  have hlc : LeadCommitMsgOk R.N S net := fun m hm hty i hi hro hct => by
    obtain ⟨c, hc, hle⟩ := hn.2.2.2.1 m hm hty i hi hro hct
    rw [memCommit_nil (hq i)] at hc; cases hc; exact hle
  exact ⟨hsh, hb.1.toB1 hq, netOkD_toB1 hs.1 hn hlc, xnetOkD_toB1 hx,
    fun n => nodeOkD_toB1 hs (hpa n) (hv n)⟩

end b1carry

end AntSim
end EtcdGrove
end Perennial

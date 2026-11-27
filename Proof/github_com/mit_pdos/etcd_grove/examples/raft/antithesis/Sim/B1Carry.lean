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

theorem netOkD_toB1 {R : RunCfg} {S : AntCheck.State} {net : List Msg} (hs : R.md.async = false)
    (h : NetOkD R S net) : NetOk R S net := by
  obtain ⟨h1, hhb, h3, h4, h5, h6, h7⟩ := h
  refine ⟨fun m hm => ?_, fun m hm hty j hj hle => (hhb m hm hty j hj).1 hle, h3, h4, h5, h6, h7⟩
  obtain ⟨hty, ⟨i, hi, -, hti⟩, j, hj, hrc⟩ := h1 m hm
  exact ⟨hty, ⟨i, hi, hti hs⟩, j, hj, fun hle => hrc (Int.le_trans (effTerm_le S j.val) hle)⟩

theorem xnetOkD_toB1 {R : RunCfg} {S : AntCheck.State} {xnet : List XMsg} (h : XNetOkD R S xnet) :
    XNetOk R S xnet := by
  intro x hx
  obtain ⟨i, hi⟩ := h x hx
  exact ⟨i, Int.le_trans hi (effTerm_le S i.val)⟩

theorem nodeFactsD_toB1 {R : RunCfg} {n : Fin R.N} {v : NodeView} (hs : SyncB1 R)
    (h : NodeFactsD R n v) : NodeFacts R n v := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  exact ⟨h1 hs.2.1, h2, h3, h4, h5, h6 hs.1, h7⟩

theorem nodeOkD_toB1 {R : RunCfg} {dec : CCDec} {S : AntCheck.State} {net : List Msg} {n : Fin R.N}
    {v : NodeView} (hs : SyncB1 R)
    (h : NodeOkD R dec S net n v) : NodeOk R dec S net n v := by
  obtain ⟨hd, hm, hsy, hu, hq, hr, hcl, hf, hl, hc, hp, -, hx, hqs, ht, hca, hxc, hlo, hvs, -⟩ := h
  have hdur : v.dur = durOf v.r := (hsy hs.1 hs.2.1 hs.2.2.1 hs.2.2.2).2.1
  refine ⟨hd, hm, hsy, hu, hq, hr, hcl, nodeFactsD_toB1 hs hf, fun hrl => ?_, fun hrc => ?_,
    hp hs.2.1, hx, hqs, ht, hca, hxc, hlo, hvs⟩
  · obtain ⟨l1, l2, l3, l4, l5⟩ := hl hrl
    refine ⟨l1, l2, l3, l4, ?_⟩
    have hlog : v.dur.log = v.r.full := by rw [hdur]; rfl
    obtain ⟨c1, c2⟩ := l5 (.inl hlog)
    exact ⟨c1, by rw [← hlog]; exact c2⟩
  · obtain ⟨c1, c2⟩ := hc hrc
    exact ⟨c1, c2 (by rw [hdur]; rfl)⟩

/-- **`AntSimD` gives `AntSim`** in a run with the B2 modes off. -/
theorem antSimD_toB1 {R : RunCfg} {dec : CCDec} {S : AntCheck.State} {V : Fin R.N → NodeView}
    {net : List Msg} {xnet : List XMsg} (hs : SyncB1 R)
    (h : AntSimD R dec S V net xnet) : AntSim R dec S V net xnet := by
  obtain ⟨hsh, hb, hn, hx, hv⟩ := h
  exact ⟨hsh, hb.1, netOkD_toB1 hs.1 hn, xnetOkD_toB1 hx, fun n => nodeOkD_toB1 hs (hv n)⟩

end b1carry

end AntSim
end EtcdGrove
end Perennial

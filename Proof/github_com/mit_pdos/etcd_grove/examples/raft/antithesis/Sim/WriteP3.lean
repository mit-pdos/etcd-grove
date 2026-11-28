/-
Lean-first (no Rocq counterpart).

# Parity B2: a `-parallel` leader's `write` (`antSim_writeP_in`)

The write of the one queued `mem` of a sync, unbatched `-parallel` leader: after `GC`, `Write` of the
queued item (`OnDisk`'s store, `wr_lstore`; nothing stored with the commit kept, `wr_lsame`, or moved,
`wr_lcommit`), and the relation after it (`od_relD`) with the node's own part (`wr_node_self`)
(#33 parity B2, Sim round 22).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.WriteP2
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.CarryD

@[expose] public section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace AntSim

open GMap go_etcd_io.raft.v3 AntCheck

section writeP3
variable [GooseExts]

set_option maxHeartbeats 4000000 in
/-- **A `-parallel` leader's write**, given that a write storing nothing has no self-acknowledgement
waiting (`hq0`). -/
theorem writeP_step {msk : SimMask} (_hmsk : msk ≤ mskB2) {R : RunCfg} {dec : CCDec} {S : State}
    {V : Fin R.N → NodeView} {net : List Msg} {xnet : List XMsg} {evs : List Event} {G : RaftFacts}
    {n : Fin R.N} {m : MemRec} {rest : List MemRec}
    (hpre : SimPreD R dec S V net xnet evs G) (hbat : R.drv.batch = false) (ha : R.md.async = false)
    (hpar : R.drv.parallel = true) (hm : (V n).mems = m :: rest)
    (hq0 : m.ents = [] → (V n).qs = []) :
    SimStepD R dec evs G (evWrite (nodeId n) m.term m.vote m.commit m.ents m.snap)
      (setV V n { V n with dur := (V n).dur.write m, undo := some (V n).dur, made := false,
                           mems := rest, jobs := markHead (V n).jobs }) net xnet := by
  obtain ⟨hp, hs0, hl, hgo0⟩ := hpre
  obtain ⟨S1, hgc, hs, hgo⟩ := antSim_gcD hbat hs0 hl hgo0
  obtain ⟨hrest, hx⟩ := wrCtx_of (hs.2.2.2.2 n) ha hbat hm
  subst hrest
  have hmt := hx.mt
  have fin : ∀ {L1 : List Entry} {c : Int} {cf : Confirmed} {M : List Fact} {p : Pre} {ch : List Entry}
      {tl : TermFn Int},
      S1.step (evWrite (nodeId n) m.term m.vote m.commit m.ents m.snap) =
        .ok (some (wrS S1 n.val L1 c cf M p ch tl [])) →
      WriteOk R S1 G n L1 c cf M p ch tl [] → L1 = logOf ((V n).dur.write m).log → c = uint.Z m.commit →
      cf.term = uint.Z (V n).ps.term ∧ ((V n).r.full.length : Int) ≤ cf.index →
      (∀ q ∈ (V n).qs, QsAckW n (V n) q →
        AckIn (wrS S1 n.val L1 c cf M p ch tl []) (nameOf (nodeId n)) (nameOf (nodeId n))
          (uint.Z (V n).ps.term) (uint.Z q.index)) →
      SimStepD R dec evs G (evWrite (nodeId n) m.term m.vote m.commit m.ents m.snap)
        (setV V n { V n with dur := (V n).dur.write m, undo := some (V n).dur, made := false,
                             mems := [], jobs := markHead (V n).jobs }) net xnet := by
    intro L1 c cf M p ch tl hstep hok hL1 hc hcf hQ
    obtain ⟨hrel, hgo2⟩ := od_relD hs hgo hok ha hbat (wr_node_self hs hok ha hbat hpar hx hL1 hc hcf hQ)
    have hv2 : (wrS S1 n.val L1 c cf M p ch tl []).viol = [] := hs.2.1.1.1
    exact ⟨_, Prefix.snoc hp hgc hstep (violated_nil hv2 hl hgo2), hrel, hgo2⟩
  have hfullE : m.ents = [] → (V n).r.full = (V n).dur.log := fun he => by
    rw [← hx.mlog]; simp only [DurW.write, he, List.head?_nil]
  have hcfE : m.ents = [] → (S1.confirmed[n.val]!).term = uint.Z (V n).ps.term ∧
      ((V n).r.full.length : Int) ≤ (S1.confirmed[n.val]!).index := fun he => by
    obtain ⟨-, -, -, -, l5⟩ := (hs.2.2.2.2 n).2.2.2.2.2.2.2.2.1 hx.hpl
    rw [hfullE he]; exact l5 (.inl (hfullE he).symm)
  have hL1E : m.ents = [] → S1.log[n.val]! = logOf ((V n).dur.write m).log := fun he => by
    rw [hx.hlog]; simp only [DurW.write, he, List.head?_nil]
  have hQE : m.ents = [] → ∀ {S₂ : State}, ∀ q ∈ (V n).qs, QsAckW n (V n) q →
      AckIn S₂ (nameOf (nodeId n)) (nameOf (nodeId n)) (uint.Z (V n).ps.term) (uint.Z q.index) :=
    by
      intro he S₂ q hq
      have h0 : (V n).qs = [] := hq0 he
      simp [h0] at hq
  by_cases hne : m.ents = []
  · have he := hne
    by_cases hcs : m.commit = (V n).dur.commit
    · obtain ⟨p, hstep, hok⟩ := wr_lsame hs hgo hx he hcs
      exact fin hstep hok (hL1E he) rfl (hcfE he) (hQE he)
    · obtain ⟨p, hstep, hok⟩ := wr_lcommit hs hgo hl hx he hcs
      exact fin hstep hok (hL1E he) rfl (hcfE he) (hQE he)
  · obtain ⟨e, es', he⟩ := List.exists_cons_of_ne_nil hne
    obtain ⟨p, hstep, hok⟩ := wr_lstore hs hgo hl hx he
    refine fin hstep hok (by rw [hx.mlog]) rfl ⟨by show uint.Z m.term = _; rw [hmt], Int.le_refl _⟩ ?_
    intro q hq h
    obtain ⟨-, -, -, -, -, -, -, hle⟩ := h
    rw [hx.hm, hx.hpar0] at hle
    have hle' : uint.nat q.index ≤ (V n).r.full.length := by
      have e1 := hx.mlog; simp only [List.append_nil, List.foldl_cons, List.foldl_nil] at hle
      rw [e1] at hle; exact hle
    refine ⟨_, mem_lset_add.mpr (.inr rfl), rfl, rfl, rfl, by show uint.Z m.term = _; rw [hmt], ?_⟩
    show uint.Z q.index ≤ ((V n).r.full.length : Int)
    have : ((uint.nat q.index : Nat) : Int) = uint.Z q.index := by word
    omega

end writeP3

end AntSim
end EtcdGrove
end Perennial

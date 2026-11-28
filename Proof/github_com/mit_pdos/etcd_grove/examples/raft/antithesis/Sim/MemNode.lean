/-
Lean-first (no Rocq counterpart).

# Parity B2: a `-parallel` leader's own part after its `mem` (`memNode_of`)

After `antSim_memP_in`'s `mem` (no write queued before it, no split write), the node's view is the
`Ready`'s drain phase with the `Ready`'s write queued (`mems = [rd.memRec]`), the disk unchanged.
`memNode_of`: its `NodeOkD` at `memQ` from the parts that depend on the kind of `Ready` (raft's facts,
the leader's part, the self-acknowledgement, the recorded commit, the queued write's result) and the
drain's facts; the rest is the old view's (the disk, the undo record, the reads, the jobs) or the
queued item (`QueueIs`: the item `Mem` queues is the record's, `memItem_eq`) (#33 parity B2, Sim
round 13).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.MemRel

@[expose] public section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace AntSim

open GMap go_etcd_io.raft.v3 AntCheck

section memNode
variable [GooseExts]

/-- **The item `Mem` queues is the record's** (`MemRec.item`): its `mem` report, and for a drain
caused by a `recv` the message handled (the binding's `pending[n]`, which the node's `told` clause
names: the cause, or the transfer message). -/
theorem memItem_eq {S : State} {N : Nat} {n : Fin N} {v : NodeView} {rd : ReadyD}
    (htold : Told v)
    (ht : v.told = true → (∃ m, v.cause = some m ∧ S.pending[n.val]! = [msgOf m (nodeId n)]) ∨
      (∃ x, v.xcause = some x ∧ S.pending[n.val]! = [xmsgOf x]))
    (hx : ∀ x, v.xcause = some x → x.dst = nodeId n ∧ v.cause = none) :
    (⟨evMem (nodeId n) v.byE (roleStr rd.pre rd.role) rd.term rd.vote rd.commit rd.ents rd.snap true,
        if v.byE == go!"recv" then S.pending[n.val]! else []⟩ : QItem) =
      MemRec.item (nodeId n) (rd.memRec v) := by
  unfold MemRec.item ReadyD.memRec
  simp only [Bool.false_eq_true, ite_false]
  congr 1
  by_cases hb : v.byE = go!"recv"
  · simp only [hb, beq_self_eq_true, ite_true]
    rcases ht (htold hb) with ⟨m, hm, hp⟩ | ⟨x, hxc, hp⟩
    · have hxn : v.xcause = none := by
        cases hxc : v.xcause with
        | none => rfl
        | some x => rw [(hx x hxc).2] at hm; cases hm
      rw [hp, hm, hxn]; rfl
    · rw [hp, hxc, (hx x hxc).2]; rfl
  · have hb' : (v.byE == go!"recv") = false := by simpa using hb
    simp only [hb', hb, Bool.false_eq_true, ite_false]

section main
variable {R : RunCfg} {dec : CCDec} {S : State} {V : Fin R.N → NodeView} {net : List Msg}
  {xnet : List XMsg} {G : RaftFacts} {n : Fin R.N} {r : MemResult} {c : Int} {i : Int}

/-- **The node's own part after a `-parallel` leader's `mem`**: the view `w` is the `Ready`'s drain
phase (any order of its messages, `P`) with its write queued; the kind-dependent parts are premises. -/
theorem memNode_of (hs : AntSimD R dec S V net xnet) (hok : MemOk R dec S V G n r c)
    (ha : R.md.async = false) (hpar : R.drv.parallel = true)
    (hm : (V n).mems = []) (htold : Told (V n))
    {r₁ : RState} {rd : ReadyD} {P : List Msg} (hrl : r₁.p.role = .leader)
    (hNF : NodeFactsD R n { ((V n).drainOf r₁ rd) with pend := P, mems := [rd.memRec (V n)] })
    (hCL : ConfLag dec R { ((V n).drainOf r₁ rd) with pend := P, mems := [rd.memRec (V n)] })
    (hLP : LeaderPartD (memQ S r n.val (MemRec.item (nodeId n) (rd.memRec (V n))) i) n
      { ((V n).drainOf r₁ rd) with pend := P, mems := [rd.memRec (V n)] })
    (hpend : R.drv.batch = false → ∀ q ∈ P, PendOk R.N (nodeId n)
      { ((V n).drainOf r₁ rd) with pend := P, mems := [rd.memRec (V n)] } q)
    (hxpend : ∀ x ∈ rd.xmsgs, XPendOk R.N (nodeId n) (accepted r₁).p x)
    (hqs : ∀ q ∈ rd.qs,
      QsOk R (memQ S r n.val (MemRec.item (nodeId n) (rd.memRec (V n))) i) n
        { ((V n).drainOf r₁ rd) with pend := P, mems := [rd.memRec (V n)] } q ∨
      QsAckW n { ((V n).drainOf r₁ rd) with pend := P, mems := [rd.memRec (V n)] } q)
    (hlead : LeadOk n { ((V n).drainOf r₁ rd) with pend := P, mems := [rd.memRec (V n)] })
    (hvself : VoteSelf n { ((V n).drainOf r₁ rd) with pend := P, mems := [rd.memRec (V n)] })
    (hDF : (V n).parts = [] → (V n).dur.write (rd.memRec (V n)) = durOf (accepted r₁))
    (hMC : MemCommitOk (memQ S r n.val (MemRec.item (nodeId n) (rd.memRec (V n))) i)
      { ((V n).drainOf r₁ rd) with pend := P, mems := [rd.memRec (V n)] }) :
    NodeOkD R dec (memQ S r n.val (MemRec.item (nodeId n) (rd.memRec (V n))) i) net n
      { ((V n).drainOf r₁ rd) with pend := P, mems := [rd.memRec (V n)] } := by
  have hsh := hs.1
  obtain ⟨d1, d2, -, d4, d5, d6, -, -, -, -, -, -, -, -, d15, d16, d17, -, -, d20, -, d22, -, d24,
    -⟩ := hs.2.2.2.2 n
  have hn6 : n.val < S.role.length := by rw [hsh.2.2.2.2.2.2.1]; exact n.isLt
  have hn13 : n.val < S.queue.length := by rw [hsh.2.2.2.2.2.2.2.2.2.2.2.2.2.1]; exact n.isLt
  refine ⟨d1, ⟨?_, d2.2.1, ?_, ?_⟩, fun _ _ _ h => absurd hpar (by rw [h]; decide), d4, ?_, d6,
    hCL, hNF, hLP, fun h => absurd h (by show r₁.p.role ≠ .candidate; rw [hrl]; decide),
    hpend, fun _ h => absurd h (List.cons_ne_nil _ _), hxpend, hqs, d15, d16, d17, hlead, hvself,
    d20, ?_, ?_, fun h => absurd h (by rw [ha]; decide), d24, hMC⟩
  · show r.role[n.val]! = roleOf r₁.p.role
    rw [hok.hrole, get!_set_self _ hn6, hrl]; rfl
  · show r.config[n.val]! = _; rw [hok.hmem.1]; exact d2.2.2.1
  · show r.confAt[n.val]! = _; rw [hok.hmem.2]; exact d2.2.2.2
  · unfold QueueIs at d5 ⊢
    show (S.queue.set n.val (S.queue[n.val]! ++ [_]))[n.val]! = _
    rw [get!_set_self _ hn13, d5, hm]; rfl
  · intro hp
    show [rd.memRec (V n)].foldl DurW.write (V n).dur = durOf (accepted r₁)
    exact hDF hp
  · obtain ⟨j1, j2, j3, j4, j5, j6⟩ := d22
    obtain ⟨hj, haj⟩ := j1 ha
    refine ⟨j1, j2, j3, fun h => absurd h (by rw [ha]; decide), ?_, fun h => absurd h (by rw [ha]; decide)⟩
    show ∀ j ∈ (V n).jobs, _
    rw [hj]; intro j hj'; cases hj'

end main

end memNode

end AntSim
end EtcdGrove
end Perennial

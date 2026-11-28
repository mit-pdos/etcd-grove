/-
Lean-first (no Rocq counterpart).

# Parity B2: `mem` evaluated (`Mem`, B 450-459)

`Mem(n, ev)` is `InMemory(n, ev)` with the node's in-memory variables set from it (`memS`) and, when
the report writes (`w = 1`), the report queued for its `write` (`OnDisk` runs then, `State.write`).
`InMemory` reads the report's fields but its name and `w`, so a `mem` report is evaluated as the
`ready` report with its fields (`inMemory_evMem`): B1's evaluations of `InMemory` per kind
(`inMemory_win`, `inMemory_lprop`, `inMemory_lcommit`) carry over (#33 parity B2, Sim round 9).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.ReadyEval
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.StmtsB2
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.Ready

@[expose] public section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace AntSim

open AntCheck

section memEval
variable [GooseExts]

/-- `InMemory` of a `mem` report is that of the `ready` report with its fields. -/
theorem inMemory_evMem (S : State) (n : Nat) (id : w64) (b r : Str) (t v c : w64) (es : List EntryM)
    (sn : Option go_etcd_io.raft.v3.entryID) (w : Bool) :
    S.inMemory n (evMem id b r t v c es sn w) = S.inMemory n (evReady id b r t v c es sn) := rfl

theorem queued_evMem (S : State) (n : Nat) (id : w64) (b r : Str) (t v c : w64) (es : List EntryM)
    (sn : Option go_etcd_io.raft.v3.entryID) (w : Bool) :
    S.queued n (evMem id b r t v c es sn w) =
      pure ⟨evMem id b r t v c es sn w, if b == go!"recv" then S.pending[n]! else []⟩ := by
  unfold State.queued
  simp only [evMem, need, pure_bind]
  split <;> rfl

/-- `Step` of a `mem` report is `Mem` at the node's position. -/
theorem step_evMem {R : RunCfg} {S : State} (n : Fin R.N) (hc : S.cfg = R.cfg) (b r : Str)
    (t v c : w64) (es : List EntryM) (sn : Option go_etcd_io.raft.v3.entryID) (w : Bool) :
    S.step (evMem (nodeId n) b r t v c es sn w) =
      (S.mem n.val (evMem (nodeId n) b r t v c es sn w) >>= fun o => match o with
        | none => pure none
        | some ns => pure (some { ns with i := S.i + 1 })) := by
  unfold State.step
  simp only [evMem, idx_name hc, State.bind, eok_bind, bne_self_eq_false, Bool.false_eq_true, ite_false]
  rfl

/-- The binding's state after `Mem`'s `InMemory` (B 452-458), before the queue. -/
def memS (S : State) (r : MemResult) : State :=
  { S with role := r.role, leaders := r.leaders, ledLog := r.ledLog, ledConf := r.ledConf,
           ledAt := r.ledAt, elAt := r.elAt, config := r.config, confAt := r.confAt,
           chain := r.chain, termLen := r.termLen, viol := r.viol }

/-- **`Mem`** (B 450-459) from `InMemory`: the in-memory variables set, and a writing report queued
(its item: the report and the message handled). -/
theorem mem_of {S : State} {n : Nat} (id : w64) (b ro : Str) (t v c : w64) (es : List EntryM)
    (sn : Option go_etcd_io.raft.v3.entryID) (w : Bool) {r : MemResult}
    (hm : S.inMemory n (evReady id b ro t v c es sn) = .ok r) (hok : r.ok = true) :
    S.mem n (evMem id b ro t v c es sn w) =
      .ok (some (if w then { memS S r with queue := S.queue.set n (S.queue[n]! ++
          [⟨evMem id b ro t v c es sn w, if b == go!"recv" then S.pending[n]! else []⟩]) }
        else memS S r)) := by
  unfold State.mem
  rw [inMemory_evMem, hm]
  rw [queued_evMem]
  cases w <;>
  simp (config := { decide := true }) only [hok, Bool.not_true, Bool.false_eq_true, ite_false,
    ite_true, eok_bind, evMem, need, pure_bind, epure, Bool.false_eq_true, ↓reduceIte] <;> rfl

/-- **A leader's term is its disk's** over `AntSimD` (any mode): its leadership record is at its
term (`LeaderPartD`), which C3 puts at most at the binding's `currentTerm` (B1's leader records), and
the disk's term is at most raft's (`NodeFactsD`). -/
theorem leader_ct {R : RunCfg} {dec : CCDec} {S : State} {V : Fin R.N → NodeView} {net : List Msg}
    {xnet : List XMsg} {k : Fin R.N} (hs : AntSimD R dec S V net xnet)
    (hvk : (V k).ps.role = .leader) : S.currentTerm[k.val]! = uint.Z (V k).ps.term := by
  have hv := hs.2.2.2.2 k
  have hkm := List.contains_iff_mem.mp (hv.2.2.2.2.2.2.2.2.1 hvk).1
  have h8 := hs.2.1.1.2.2.2.2.2.2.2.1 k _ hkm rfl
  have hd : S.currentTerm[k.val]! = uint.Z (V k).dur.term := hv.1.1
  have hle : uint.Z (V k).dur.term ≤ uint.Z (V k).ps.term := hv.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.1
  dsimp only at h8
  omega

/-- **The leader of a term is unique** over `AntSimD` (`lead_unique` without the disks' being raft's
states). -/
theorem lead_uniqueD {R : RunCfg} {dec : CCDec} {S : State} {V : Fin R.N → NodeView} {net : List Msg}
    {xnet : List XMsg} {G : RaftFacts} {n k : Fin R.N}
    (hs : AntSimD R dec S V net xnet) (hgo : GlobalOk R S net G) (hl : RaftLaws G)
    (hk : S.role[k.val]! = leader)
    (hn : S.leaders.contains { server := nameOf (nodeId n), term := S.currentTerm[k.val]! } = true) :
    k = n := by
  have hv := hs.2.2.2.2 k
  have hvk : (V k).ps.role = .leader := by
    have h := hv.2.1.1
    rw [hk] at h
    exact (roleOf_leader_iff _).mp h.symm
  have hkm := List.contains_iff_mem.mp (hv.2.2.2.2.2.2.2.2.1 hvk).1
  have hnm := List.contains_iff_mem.mp hn
  have h := hgo.leader_server hl hnm hkm (leader_ct hs hvk)
  exact name_inj h.symm

end memEval

end AntSim
end EtcdGrove
end Perennial

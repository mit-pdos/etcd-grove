/-
Lean-first (no Rocq counterpart).

# The refinement to Antithesis's binding: `recv` (#33 S4, the invariant phase)

`antSim_recv` (`Stmts.lean`): the message a node handles, sent to it, is reported (`reportCause`,
`evRecv`) and taken (`Recv`, B 199-204): after the `GC` steps due (`antSim_gc`), its `to` is the
node; a request (`app`, `hb`; no snapshot is ever sent, C4) of a term at least the node's is
`Sendable`, which C4 keeps for every message while its receiver has not passed its term. `Recv` sets
`pending[n]` to it, which the node's view now says (`told`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.Boot

@[expose] public section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace AntSim

open AntCheck

section recv
variable [GooseExts]

theorem typ_msgOf (m : Msg) (to : w64) : (msgOf m to).typ = .ok (msgTypeStr m.ty) := rfl

theorem msgTypeStr_snap {t : MsgType} (h : t ≠ .snap) : (msgTypeStr t == go!"snap") = false := by
  cases t <;> first | exact absurd rfl h | decide

theorem isReq_msgOf (m : Msg) (to : w64) (h : m.ty ≠ .snap) :
    isReq (msgOf m to) = .ok (decide (m.ty = .app ∨ m.ty = .heartbeat)) := by
  unfold isReq
  rw [typ_msgOf, eok_bind]
  cases hty : m.ty <;> first | exact absurd hty h | rfl

theorem snapOk_msgOf (ll : TermFn (List Entry)) (m : Msg) (to : w64) (h : m.ty ≠ .snap) :
    snapOk ll (msgOf m to) = .ok true := by
  unfold snapOk
  rw [typ_msgOf, eok_bind]
  have := msgTypeStr_snap h
  simp only [bne, this, Bool.not_false, if_true, epure]

theorem reqFactIn_msgOf (ll : TermFn (List Entry)) (m : Msg) (to : w64) (h : m.ty ≠ .snap) :
    reqFactIn ll (msgOf m to) = toAppendFact (msgOf m to) := by
  unfold reqFactIn
  rw [typ_msgOf, eok_bind]
  have := msgTypeStr_snap h
  simp only [this, Bool.false_eq_true, if_false]

/-- What `Recv` leaves: `pending[n]` the message (and `i`). -/
def recvS (S : State) (n : Nat) (m : AntCheck.Msg) : State :=
  { S with pending := S.pending.set n [m], i := S.i + 1 }

theorem recv_eq {S : State} (n : Fin 3) (m : Msg) (hc : S.cfg = cfg3) (hty : m.ty ≠ .snap)
    (hreq : (m.ty = .app ∨ m.ty = .heartbeat) → S.currentTerm[n.val]! ≤ uint.Z m.term →
      (toAppendFact (msgOf m (nodeId n)) >>= S.sendable) = .ok true) :
    S.step (evRecv (nodeId n) m) = .ok (some (recvS S n.val (msgOf m (nodeId n)))) := by
  unfold State.step
  simp (config := { decide := true }) only [evRecv, idx_name hc, State.bind, State.recv, eok_bind, epure,
    ite_true, ite_false, need, Bool.false_eq_true]
  have hto : (msgOf m (nodeId n)).to_ = .ok (nameOf (nodeId n)) := rfl
  have hterm : (msgOf m (nodeId n)).term_ = .ok (uint.Z m.term) := rfl
  have hand : AntCheck.andM (.ok (decide (m.ty = .app ∨ m.ty = .heartbeat)))
      (.ok (decide (uint.Z m.term ≥ S.currentTerm[n.val]!))) =
      .ok (decide ((m.ty = .app ∨ m.ty = .heartbeat) ∧ S.currentTerm[n.val]! ≤ uint.Z m.term)) := by
    by_cases h1 : m.ty = .app ∨ m.ty = .heartbeat <;>
      by_cases h2 : S.currentTerm[n.val]! ≤ uint.Z m.term <;> simp [h1, h2, andM_true, andM_false]
  simp only [hto, server_of hc n, bne_self_eq_false, isReq_msgOf _ _ hty, hterm, eok_bind, ite_false,
    Bool.false_eq_true, epure, hand]
  by_cases hq : (m.ty = .app ∨ m.ty = .heartbeat) ∧ S.currentTerm[n.val]! ≤ uint.Z m.term
  · have h1 := hreq hq.1 hq.2
    rw [toAppendFact_msgOf, eok_bind] at h1
    simp only [hq, decide_true, ite_true, snapOk_msgOf _ _ _ hty, reqFactIn_msgOf _ _ _ hty, toAppendFact_msgOf,
      eok_bind, h1, andM_true, Bool.not_true, Bool.false_eq_true, ite_false]
    rfl
  · simp only [hq, decide_false, Bool.false_eq_true, ite_false]
    rfl

/-- **`recv`** (B 199-204). -/
theorem antSim_recv : antSim_recv.stmt := by
  intro S V net evs G n m hp hs hl hgo hm hdst hcause
  obtain ⟨S1, hgc, hs1, hgo1⟩ := antSim_gc S V net G hs hl hgo
  obtain ⟨hsh, hb, hn, hno⟩ := hs1
  have hc : S1.cfg = cfg3 := hsh.1
  obtain ⟨hty, _, j, hj, hjk⟩ := hn m hm
  have hjn : j = n := nodeId_inj (hj.symm.trans hdst)
  subst hjn
  have hsnap : m.ty ≠ .snap := by
    rcases hty with h | h | h | h | h | h | h <;> rw [h] <;> decide
  have hstep := recv_eq j m hc hsnap (fun ht hle => by
    have := (hjk hle).1 ht
    rw [hj] at this; exact this)
  have hrel : AntSim (recvS S1 j.val (msgOf m (nodeId j))) (setV V j { V j with told := true }) net := by
    obtain ⟨sh0, sh1, sh2, sh3, sh4, sh5, sh6, sh7, sh8, sh9, sh10, sh11, sh12, sh13, sh14⟩ := hsh
    refine ⟨⟨sh0, sh1, sh2, sh3, sh4, sh5, sh6, sh7, sh8, sh9, sh10, sh11,
      by simpa [recvS] using sh12, sh13, sh14⟩, hb, hn, fun k => ?_⟩
    obtain ⟨d1, d2, d3, d4, d5, d6, d7⟩ := hno k
    by_cases hk : k = j
    · subst hk
      simp only [setV, ite_true]
      refine ⟨d1, d2, d3, d4, d5, fun _ => ⟨m, hcause, ?_⟩, d7⟩
      change (S1.pending.set k.val [msgOf m (nodeId k)])[k.val]! = _
      exact get!_set_self _ (by rw [sh12]; exact k.isLt)
    · simp only [setV, hk, ite_false]
      refine ⟨d1, d2, d3, d4, d5, fun ht => ?_, d7⟩
      obtain ⟨m', hm1, hm2⟩ := d6 ht
      refine ⟨m', hm1, ?_⟩
      change (S1.pending.set j.val [msgOf m (nodeId j)])[k.val]! = _
      rw [get!_set_ne _ _ (fun h => hk (Fin.ext h))]; exact hm2
  have hgo2 : GlobalOk (recvS S1 j.val (msgOf m (nodeId j))) net G := hgo1
  exact ⟨_, Prefix.snoc hp hgc hstep (violated_nil hb.1 hl hgo2), hrel, hgo2⟩

end recv

end AntSim
end EtcdGrove
end Perennial

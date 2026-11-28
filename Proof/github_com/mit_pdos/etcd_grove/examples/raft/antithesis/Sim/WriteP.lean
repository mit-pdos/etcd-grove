/-
Lean-first (no Rocq counterpart).

# Parity B2: a `-parallel` leader's `write` (`Write`, B 462-470), its evaluation

A `-parallel` leader's `mem` queues its `Ready`'s item (`antSim_memP_in`); the storage goroutine's
`write` report pops it and runs `OnDisk` on it (B 462-470) with the binding's current in-memory
variables. `OnDisk` reads only the item's term, vote, commit, role, snapshot, first index and
entries, which a `mem` report has as the `ready` report with its fields does (`onDisk_evMem`, by
`rfl`), so the B1 `OnDisk` evaluations of a leader's `Ready` (`onDisk_lstore`, `onDisk_lcommit`)
apply. `write_of`: `Write` from `OnDisk` (the report's fields are the item's) (#33 parity B2, Sim
round 19).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.MemP
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.Apply

@[expose] public section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace AntSim

open GMap go_etcd_io.raft.v3 AntCheck

section writeP
variable [GooseExts]

set_option maxHeartbeats 2000000 in
/-- `OnDisk` does not read a report's kind or `w` field (by `rfl`: every read is a projection of
another field). -/
theorem onDisk_ew (S : State) (n : Nat) (ev : Event) (e' : Str) (w' : Option Int) (M : List AntCheck.Msg)
    (more : Bool) (ro : List Str) (ld : List LeaderRec) (ll : TermFn (List Entry)) (ch : List Entry)
    (tl : TermFn Int) (vi : SSet) :
    S.onDisk n ⟨{ ev with e := e', w := w' }, M⟩ more ro ld ll ch tl vi = S.onDisk n ⟨ev, M⟩ more ro ld ll ch tl vi :=
  rfl

/-- `OnDisk` of a `mem` report's item is that of the `ready` report with its fields. -/
theorem onDisk_evMem (S : State) (n : Nat) (id : w64) (b r : Str) (t v c : w64) (es : List EntryM)
    (sn : Option go_etcd_io.raft.v3.entryID) (w : Bool) (M : List AntCheck.Msg) (more : Bool)
    (ro : List Str) (ld : List LeaderRec) (ll : TermFn (List Entry)) (ch : List Entry) (tl : TermFn Int)
    (vi : SSet) :
    S.onDisk n ⟨evMem id b r t v c es sn w, M⟩ more ro ld ll ch tl vi =
      S.onDisk n ⟨evReady id b r t v c es sn, M⟩ more ro ld ll ch tl vi := by
  have e1 : evMem id b r t v c es sn w =
      { evReady id b r t v c es sn with e := go!"mem", w := some (if w then 1 else 0) } := rfl
  rw [e1]
  exact onDisk_ew _ _ _ _ _ _ _ _ _ _ _ _ _

/-- `Step` of a `write` report is `Write` at the node's position. -/
theorem step_evWrite {R : RunCfg} {S : State} (n : Fin R.N) (hc : S.cfg = R.cfg) (t v c : w64)
    (es : List EntryM) (sn : Option go_etcd_io.raft.v3.entryID) :
    S.step (evWrite (nodeId n) t v c es sn) =
      (S.write n.val (evWrite (nodeId n) t v c es sn) >>= fun o => match o with
        | none => pure none
        | some ns => pure (some { ns with i := S.i + 1 })) := by
  unfold State.step
  simp only [evWrite, idx_name hc, State.bind, eok_bind, bne_self_eq_false, Bool.false_eq_true, ite_false]
  rfl

/-- **`Write`** (B 462-470) of the report of the head item's write: `OnDisk` of the item with the
binding's in-memory variables, the item popped. -/
theorem write_of {S : State} {n : Nat} (id : w64) (b ro : Str) (t v c : w64) (es : List EntryM)
    (sn : Option go_etcd_io.raft.v3.entryID) (M : List AntCheck.Msg) (rest : List QItem) {ns : State}
    (hq : S.queue[n]! = ⟨evMem id b ro t v c es sn true, M⟩ :: rest)
    (hod : S.onDisk n ⟨evReady id b ro t v c es sn, M⟩ false S.role S.leaders S.ledLog S.chain S.termLen
      S.viol = .ok (some ns)) :
    S.write n (evWrite id t v c es sn) = .ok (some { ns with queue := S.queue.set n rest }) := by
  unfold State.write
  rw [hq]
  simp only [evWrite, evMem, need, beq_self_eq_true, entriesEqual_self, eok_bind, epure,
    od_andM_ok, Bool.and_true, Bool.not_true, Bool.false_eq_true, ite_false]
  have h := onDisk_evMem S n id b ro t v c es sn true M false S.role S.leaders S.ledLog S.chain S.termLen S.viol
  rw [hod] at h
  simp only [evMem] at h
  rw [h]
  rfl

end writeP

end AntSim
end EtcdGrove
end Perennial

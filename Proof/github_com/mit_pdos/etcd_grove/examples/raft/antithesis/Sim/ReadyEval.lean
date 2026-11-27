/-
Lean-first (no Rocq counterpart).

# The refinement to Antithesis's binding: `ready` evaluated, per kind (#33 S4, the invariant phase)

`Ready` (B 439-447: `InMemory`, B 213-275, then `OnDisk`, B 290-436) of a `ready` report
(`evReady`), evaluated to its successor for each kind of `Ready` raft makes
(`notes/antithesis-rawnode-design.md` §3.3, "`antSim_ready`, guard by guard"). A `ready` report's
`entries` field is always present, so `OnDisk`'s `bat` is false and its `isApp`, `below`, `takes`
are false: the entries are the report's, from its `first`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.Logs
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.Boot
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.SendRel

@[expose] public section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace AntSim

open AntCheck

section eval
variable [GooseExts]

theorem roleOf_ne_precand (r : Role) : (roleOf r == go!"precandidate") = false := by
  cases r <;> decide

theorem str_beq (a b : Str) : (a == b) = decide (a = b) := Bool.eq_iff_iff.mpr (by simp)
theorem str_bne (a b : Str) : (a != b) = !decide (a = b) := by rw [bne, str_beq]

theorem ready_name_ne {R : RunCfg} (j : Fin R.N) : (nameOf (nodeId j) != []) = true := by
  unfold nameOf; rw [if_neg (nodeId_ne_zero j)]; simp

/-- `Step` of a `ready` report is `Ready` at the node's position. -/
theorem step_evReady {R : RunCfg} {S : State} (n : Fin R.N) (hc : S.cfg = R.cfg) (b : Str) (r : Str)
    (t v c : w64) (es : List EntryM) :
    S.step (evReady (nodeId n) b r t v c es) =
      (S.ready n.val (evReady (nodeId n) b r t v c es) >>= fun o => match o with
        | none => pure none
        | some ns => pure (some { ns with i := S.i + 1 })) := by
  unfold State.step
  simp only [evReady, idx_name hc, State.bind, eok_bind, bne_self_eq_false, Bool.false_eq_true, ite_false]
  rfl

/-- What `InMemory` gives for a report of a non-leader role (`leads`, `wins`, `app`, `cmt` false):
the role, and nothing else changed (a candidate's report at a node of the configuration is not
`Unpromotable`). -/
def memNL (S : State) (n : Nat) (r : Str) : MemResult :=
  { ok := true, role := S.role.set n r, leaders := S.leaders, ledLog := S.ledLog, ledConf := S.ledConf,
    config := S.config, confAt := S.confAt, ledAt := S.ledAt, elAt := S.elAt, chain := S.chain,
    termLen := S.termLen, viol := S.viol }

set_option maxHeartbeats 2000000 in
/-- (parity B1) A candidate's report at a node outside its configuration would be `Unpromotable`:
the premise `hunp` (raft campaigns only at a voter). -/
theorem inMemory_nl_eq {R : RunCfg} {S : State} (n : Fin R.N) (hc : S.cfg = R.cfg) (b : Str)
    (hb : DrainBy b)
    (r : Role) (hr : r ≠ .leader) (t v c : w64) (es : List EntryM)
    (hunp : r = .candidate → ((S.config[n.val]!).cin.has (nameOf (nodeId n)) ||
      (S.config[n.val]!).cout.has (nameOf (nodeId n))) = true) :
    S.inMemory n.val (evReady (nodeId n) b (roleOf r) t v c es) = .ok (memNL S n.val (roleOf r)) := by
  unfold State.inMemory
  cases r
  case leader => exact absurd rfl hr
  case follower =>
    rcases drainBy_cases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp (config := { decide := true }) only [evReady, InMem.ok, InMem.T, InMem.role1, InMem.leads,
      InMem.wins, InMem.es, InMem.ld1, InMem.ll1, InMem.lc1, InMem.snapsM, InMem.app, InMem.ll2,
      InMem.cmt, fieldEq, need, eok_bind, epure, roleOf, str_beq, str_bne, leader, follower, candidate,
      decide_false, decide_true, Bool.not_true, Bool.not_false,
      Bool.false_eq_true, ite_true, ite_false, andM_false, andM_true, orM_true, orM_false, memNL, server_of hc n,
      Option.isSome_none, Option.map_none, Bool.false_and,
      Bool.and_false, Bool.true_and, Bool.and_true]
  case candidate =>
    have hunp := hunp rfl
    rcases drainBy_cases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp (config := { decide := true }) only [evReady, InMem.ok, InMem.T, InMem.role1, InMem.leads,
      InMem.wins, InMem.es, InMem.ld1, InMem.ll1, InMem.lc1, InMem.snapsM, InMem.app, InMem.ll2,
      InMem.cmt, fieldEq, need, eok_bind, epure, roleOf, str_beq, str_bne, leader, follower, candidate,
      decide_false, decide_true, Bool.not_true, Bool.not_false,
      Bool.false_eq_true, ite_true, ite_false, andM_false, andM_true, orM_true, orM_false, memNL, server_of hc n,
      Option.isSome_none, Option.map_none, Bool.false_and,
      Bool.and_false, hunp, Bool.true_and, Bool.and_true]

/-! ## A pre-candidate's report is a follower's (B 248-250 `role1`) -/

/-- `InMemory` reads a report's role through `role1` (a pre-candidate a follower), `leads` and the
`Unpromotable` test, which a pre-candidate's and a follower's report pass alike. -/
theorem inMemory_pre_eq (S : State) (n : Nat) (id : w64) (b : Str) (t v c : w64) (es : List EntryM)
    (sn : Option go_etcd_io.raft.v3.entryID) :
    S.inMemory n (evReady id b go!"precandidate" t v c es sn) =
      S.inMemory n (evReady id b go!"follower" t v c es sn) := rfl

set_option maxHeartbeats 2000000 in
/-- `OnDisk` reads the report's role only in `elect` and `leads`, false for both. -/
theorem onDisk_pre_eq (S : State) (n : Nat) (id : w64) (b : Str) (t v c : w64) (es : List EntryM)
    (sn : Option go_etcd_io.raft.v3.entryID) (M : List AntCheck.Msg) (more : Bool) (ro : List Str) (ld : List LeaderRec)
    (ll : TermFn (List Entry)) (ch : List Entry) (tl : TermFn Int) (vi : SSet) :
    S.onDisk n ⟨evReady id b go!"precandidate" t v c es sn, M⟩ more ro ld ll ch tl vi =
      S.onDisk n ⟨evReady id b go!"follower" t v c es sn, M⟩ more ro ld ll ch tl vi := rfl

theorem queued_evReady (S : State) (n : Nat) (id : w64) (b r : Str) (t v c : w64) (es : List EntryM)
    (sn : Option go_etcd_io.raft.v3.entryID) :
    S.queued n (evReady id b r t v c es sn) =
      pure ⟨evReady id b r t v c es sn, if b == go!"recv" then S.pending[n]! else []⟩ := by
  unfold State.queued
  simp only [evReady, need, pure_bind]
  split <;> rfl

/-- **A pre-candidate's `ready` report is evaluated as a follower's.** -/
theorem ready_pre_eq (S : State) (n : Nat) (id : w64) (b : Str) (t v c : w64) (es : List EntryM)
    (sn : Option go_etcd_io.raft.v3.entryID) :
    S.ready n (evReady id b go!"precandidate" t v c es sn) =
      S.ready n (evReady id b go!"follower" t v c es sn) := by
  unfold State.ready
  rw [inMemory_pre_eq, queued_evReady, queued_evReady]
  simp only [pure_bind, onDisk_pre_eq]

end eval

end AntSim
end EtcdGrove
end Perennial

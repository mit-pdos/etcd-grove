/-
Lean-first (no Rocq counterpart).

# The refinement to Antithesis's binding: `boot` (#33 S4, the invariant phase)

`antSim_boot` (`Stmts.lean`): a fresh node's `boot` report (`RunCluster`, `evBoot`) is taken
(`Boot`, B 162-194): after the `GC` steps due (`antSim_gc`), `Recovered` holds of the node's own
variables (C1: term 0, no vote, commit 0, an empty log), nothing was applied, the configuration
is `InitConf` (voters `names(3)`, none outgoing). `Boot` resets the node's announced write,
pending message, queues and role (already follower), which C1-C5 hold of trivially.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.Init

@[expose] public section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace AntSim

open AntCheck

/-- The state `Boot` leaves at node `n` with nothing to recover from an announced write and nothing
applied: the announced write, pending message, queues taken back, the role follower, `lastApplied`
0, the initial configuration. -/
def bootRes (S : State) (n : Nat) : State :=
  { S with undo := S.undo.set n none, pending := S.pending.set n [], queue := S.queue.set n [],
           reads := S.reads.set n [], role := S.role.set n follower, lastApplied := S.lastApplied.set n 0,
           config := S.config.set n S.initConf, confAt := S.confAt.set n 0 }

/-- What `Boot` changes under C1 at a fresh node: the announced write, the pending message, `i`. -/
def bootS (S : State) (n : Nat) : State :=
  { S with undo := S.undo.set n none, pending := S.pending.set n [], i := S.i + 1 }

theorem andM_true (b : EvalM Bool) : AntCheck.andM (.ok true) b = b := by unfold AntCheck.andM; cases b <;> rfl
theorem andM_false (b : EvalM Bool) : AntCheck.andM (.ok false) b = .ok false := rfl
theorem orM_true (b : EvalM Bool) : AntCheck.orM (.ok true) b = .ok true := rfl
theorem orM_false (b : EvalM Bool) : AntCheck.orM (.ok false) b = b := by unfold AntCheck.orM; cases b <;> rfl

theorem confOf_zero (l : List Entry) (c : Conf) : confOf l 0 c = .ok c := rfl
theorem lastConf_zero (l : List Entry) : lastConf l 0 = .ok 0 := rfl

theorem boot_eq {S : State} (n : Fin 3) (hc : S.cfg = cfg3) (hct : S.currentTerm[n.val]! = 0)
    (hv : S.vote n.val = []) (hci : S.commitIndex[n.val]! = 0) (hl : S.log[n.val]! = []) :
    S.step (evBoot (nodeId n)) = .ok (some { bootRes S n.val with i := S.i + 1 }) := by
  have hconf : S.initConf = { cin := setOf (namesL 3), cout := [] } := by
    unfold State.initConf Config.initConf; rw [hc]; rfl
  have hset0 : setOf [] = [] := rfl
  have hz : ((([] : List Entry).length : Nat) : Int) = 0 := rfl
  unfold State.step
  simp (config := { decide := true }) only [evBoot, idx_name hc, State.bind, State.boot, recovered,
    fieldEq, need, hct, hv, hci, hl, eok_bind, epure, ite_true, ite_false, beq_self_eq_true, andM_true,
    orM_true, Bool.not_true, Bool.false_eq_true, termAt, confOf_zero, lastConf_zero, hz, hconf, sameConf,
    hset0, Option.isSome_some, Bool.not_false]
  simp only [bootRes, hconf]


/-! ## Lists set at one position -/

theorem get!_set_self {α : Type} [Inhabited α] {l : List α} {n : Nat} (x : α) (h : n < l.length) :
    (l.set n x)[n]! = x := by
  rw [getElem!_pos (l.set n x) n (by simpa using h), List.getElem_set_self]

theorem get!_set_ne {α : Type} [Inhabited α] (l : List α) {n j : Nat} (x : α) (h : j ≠ n) :
    (l.set n x)[j]! = l[j]! := by
  simp only [getElem!_def, List.getElem?_set_ne (Ne.symm h)]

theorem set_get!_self {α : Type} [Inhabited α] {l : List α} {n : Nat} (h : n < l.length) :
    l.set n l[n]! = l := by
  rw [getElem!_pos l n h]; exact List.set_getElem_self h

section boot
variable [GooseExts]

/-- **`boot`** (B 162-194). -/
theorem antSim_boot : antSim_boot.stmt := by
  intro S V net evs G n hp hs hl hgo hpi hdel hidle htold
  obtain ⟨S1, hgc, hs1, hgo1⟩ := antSim_gc S V net G hs hl hgo
  obtain ⟨hsh, hb, hn, hno⟩ := hs1
  have hc : S1.cfg = cfg3 := hsh.1
  obtain ⟨hd, _⟩ := hno n
  obtain ⟨hterm, hvote, _, hrole, _, _, _, hlog, hcommit, _⟩ := hpi
  have hct : S1.currentTerm[n.val]! = 0 := by rw [hd.1, hterm]; rfl
  have hvt : S1.vote n.val = [] := by rw [hd.2.1, hvote]; unfold nameOf; simp
  have hci : S1.commitIndex[n.val]! = 0 := by rw [hd.2.2.2.1, hcommit]; rfl
  have hlg : S1.log[n.val]! = [] := by rw [hd.2.2.1, hlog]; rfl
  have hn3 : n.val < 3 := n.isLt
  -- `Boot` changes only the announced write and the pending message (and `i`).
  have hS2 : { bootRes S1 n.val with i := S1.i + 1 } = bootS S1 n.val := by
    have hq : S1.queue.set n.val [] = S1.queue := by
      conv => lhs; rw [← (hb.2.1 n).1]
      exact set_get!_self (by rw [hsh.2.2.2.2.2.2.2.2.2.2.2.2.2.1]; exact hn3)
    have hr : S1.reads.set n.val [] = S1.reads := by
      conv => lhs; rw [← (hb.2.1 n).2]
      exact set_get!_self (by rw [hsh.2.2.2.2.2.2.2.2.2.2.2.2.2.2]; exact hn3)
    have hro : S1.role.set n.val follower = S1.role := by
      have : S1.role[n.val]! = follower := by rw [hd.2.2.2.2.1, hrole]; rfl
      conv => lhs; rw [← this]
      exact set_get!_self (by rw [hsh.2.2.2.2.2.2.1]; exact hn3)
    have hla : S1.lastApplied.set n.val 0 = S1.lastApplied := by
      have : S1.lastApplied[n.val]! = 0 := by rw [hd.2.2.2.2.2.1, hdel]; rfl
      conv => lhs; rw [← this]
      exact set_get!_self (by rw [hsh.2.2.2.2.2.2.2.1]; exact hn3)
    have hco : S1.config.set n.val S1.initConf = S1.config := by
      have : S1.config[n.val]! = S1.initConf := by
        rw [hd.2.2.2.2.2.2.2.2.2.1]; unfold State.initConf; rw [hc]
      conv => lhs; rw [← this]
      exact set_get!_self (by rw [hsh.2.2.2.2.2.2.2.2.1]; exact hn3)
    have hca : S1.confAt.set n.val 0 = S1.confAt := by
      have : S1.confAt[n.val]! = 0 := hd.2.2.2.2.2.2.2.2.2.2.1
      conv => lhs; rw [← this]
      exact set_get!_self (by rw [hsh.2.2.2.2.2.2.2.2.2.1]; exact hn3)
    unfold bootRes bootS
    rw [hq, hr, hro, hla, hco, hca]
  have hstep := boot_eq n hc hct hvt hci hlg
  rw [hS2] at hstep
  obtain ⟨sh0, sh1, sh2, sh3, sh4, sh5, sh6, sh7, sh8, sh9, sh10, sh11, sh12, sh13, sh14⟩ := hsh
  obtain ⟨hb1, hb2, hb3, hb4⟩ := hb
  have hgo2 : GlobalOk (bootS S1 n.val) net G := hgo1
  have hrel : AntSim (bootS S1 n.val) V net := by
    refine ⟨⟨sh0, sh1, sh2, sh3, sh4, sh5, sh6, sh7, sh8, sh9, sh10, by simpa [bootS] using sh11,
      by simpa [bootS] using sh12, sh13, sh14⟩, ⟨hb1, hb2, ?_, hb4⟩, hn, fun j => ?_⟩
    · intro j p hp
      by_cases hj : j = n
      · subst hj
        change (S1.undo.set j.val none)[j.val]! = some p at hp
        rw [get!_set_self _ (by rw [sh11]; exact j.isLt)] at hp; cases hp
      · change (S1.undo.set n.val none)[j.val]! = some p at hp
        rw [get!_set_ne _ _ (fun h => hj (Fin.ext h))] at hp
        exact hb3 j p hp
    · obtain ⟨d1, d2, d3, d4, d5, d6⟩ := hno j
      refine ⟨d1, d2, d3, d4, d5, fun ht => ?_⟩
      by_cases hj : j = n
      · subst hj; rw [htold] at ht; cases ht
      · obtain ⟨m, hm1, hm2⟩ := d6 ht
        refine ⟨m, hm1, ?_⟩
        change (S1.pending.set n.val [])[j.val]! = _
        rw [get!_set_ne _ _ (fun h => hj (Fin.ext h))]; exact hm2
  exact ⟨_, Prefix.snoc hp hgc hstep (violated_nil hb1 hl hgo2), hrel, hgo2⟩

end boot

end AntSim
end EtcdGrove
end Perennial

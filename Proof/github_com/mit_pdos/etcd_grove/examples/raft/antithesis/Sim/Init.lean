/-
Lean-first (no Rocq counterpart).

# The refinement to Antithesis's binding: the initial state (#33 S4, the invariant phase)

`antSim_init` (`Stmts.lean`): `Init0` (B 755, `Bootstrapped = FALSE`) is the model's `Init`
(R 181-201), every node at term 0, no vote, an empty log, follower, nothing recorded; three fresh
nodes (`PInit`) are related to it, and its facts (one empty log per node) are certified by any `G`
that has the empty log.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.GC

@[expose] public section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace AntSim

open AntCheck

/-- `Init0 cfg3`'s state. -/
def initS : State :=
  let n := cfg3.server.length
  { cfg := cfg3, currentTerm := List.replicate n 0, voteTerm := List.replicate n 0,
    voteFor := List.replicate n [], log := List.replicate n [],
    commitIndex := List.replicate n 0, role := List.replicate n follower,
    lastApplied := List.replicate n 0, config := List.replicate n cfg3.initConf,
    confAt := List.replicate n 0, confirmed := List.replicate n {},
    msgs := [], votes := [], leaders := [], ledLog := [], ledConf := [], ledAt := [], elAt := [],
    i := 1, undo := List.replicate n none, pending := List.replicate n [],
    queue := List.replicate n [], reads := List.replicate n [], chain := [], termLen := [],
    viol := [] }

theorem init0_cfg3 : init0 cfg3 = .ok initS := rfl

theorem rep3_length {α : Type} (x : α) : (List.replicate cfg3.server.length x).length = 3 := by
  rw [List.length_replicate, cfg3_server, namesL_length]

theorem rep3_get {α : Type} [Inhabited α] (x : α) (n : Fin 3) :
    (List.replicate cfg3.server.length x)[n.val]! = x := by
  rw [cfg3_server, namesL_length]
  match n with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl
  | ⟨2, _⟩ => rfl

theorem nameOf_zero : nameOf (W64 0) = [] := by unfold nameOf; simp

theorem nodeId_ne_zero : ∀ n : Fin 3, nodeId n ≠ W64 0 := by decide +kernel

theorem prefix_init : Prefix cfg3 [] initS :=
  ⟨{ state := initS }, by rw [init0_cfg3]; rfl, rfl, rfl⟩

section init
variable [GooseExts]

/-- **The initial state** (B 755). -/
theorem antSim_init : antSim_init.stmt := by
  intro V hV
  refine ⟨initS, prefix_init, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · exact ⟨rfl, rep3_length _, rep3_length _, rep3_length _, rep3_length _, rep3_length _,
      rep3_length _, rep3_length _, rep3_length _, rep3_length _, rep3_length _, rep3_length _,
      rep3_length _, rep3_length _, rep3_length _⟩
  · refine ⟨rfl, fun n => ⟨rep3_get _ n, rep3_get _ n⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro n p hp
      change (List.replicate cfg3.server.length (none : Option Pre))[n.val]! = some p at hp
      rw [rep3_get] at hp; cases hp
    · intro p hp; cases hp
    · intro n
      have h0 : initS.commitIndex[n.val]! = 0 := rep3_get _ n
      have hl : initS.log[n.val]! = [] := rep3_get _ n
      rw [h0, hl]; exact ⟨Int.le_refl _, rfl⟩
    · intro n
      left; exact rep3_get _ n
    · intro n l hl
      change TermFn.get ([] : TermFn (List Entry)) _ = _ at hl
      cases hl
    · intro n a ha; cases ha
    · intro p hp; cases hp
    · intro n l hl; cases hl
    · intro f hf; cases hf
    · intro v hv; cases hv
    · intro n hv
      have h0 : initS.currentTerm[n.val]! = 0 := rep3_get _ n
      have hv0 : initS.voteTerm[n.val]! = 0 := rep3_get _ n
      have hbt : initS.bootTerm = 0 := rfl
      exfalso; apply hv
      unfold State.vote State.voteOf
      rw [h0, hv0, hbt]; rfl
    · intro n a ha; cases ha
    · intro n
      have h0 : initS.currentTerm[n.val]! = 0 := rep3_get _ n
      have hv0 : initS.voteTerm[n.val]! = 0 := rep3_get _ n
      rw [h0, hv0]; exact Int.le_refl _
    · intro j
      have h0 : initS.currentTerm[j.val]! = 0 := rep3_get _ j
      have hc0 : initS.confirmed[j.val]! = {} := rep3_get _ j
      rw [h0, hc0]; exact ⟨.inl rfl, Int.le_refl _⟩
  · unfold NetOk HbCommitOk NetShape
    refine ⟨?_, ?_, ?_⟩ <;> intro m hm <;> cases hm
  · intro n
    obtain ⟨⟨hterm, hvote, hlead, hrole, _, hout, hbase, hlog, hcommit, _⟩, hdel, ⟨hqs, hpend, hce⟩, htold, hcause⟩ :=
      hV n
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, hout, hbase, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
    · change (List.replicate cfg3.server.length (0 : Int))[n.val]! = _
      rw [rep3_get, hterm]; rfl
    · have h0 : initS.currentTerm[n.val]! = 0 := rep3_get _ n
      have hv0 : initS.voteTerm[n.val]! = 0 := rep3_get _ n
      have hbt : initS.bootTerm = 0 := rfl
      rw [hvote, nameOf_zero]
      unfold State.vote State.voteOf
      rw [h0, hv0, hbt]; rfl
    · change (List.replicate cfg3.server.length ([] : List Entry))[n.val]! = _
      rw [rep3_get, hlog]; rfl
    · change (List.replicate cfg3.server.length (0 : Int))[n.val]! = _
      rw [rep3_get, hcommit]; rfl
    · change (List.replicate cfg3.server.length follower)[n.val]! = _
      rw [rep3_get, hrole]; rfl
    · change (List.replicate cfg3.server.length (0 : Int))[n.val]! = _
      rw [rep3_get, hdel]; rfl
    · rw [hlog]; intro k e he; cases he
    · exact rep3_get _ n
    · exact rep3_get _ n
    · rw [hdel, hce, hlog]; exact List.prefix_refl _
    · rw [hdel, hce]; exact Nat.zero_le _
    · intro h; rw [hrole] at h; cases h
    · intro h; rw [hrole] at h; cases h
    · rw [hpend]; intro q hq; cases hq
    · rw [hqs]; intro q hq; cases hq
    · refine ⟨?_, ?_, ?_⟩
      · rw [htold]; intro h; cases h
      · rw [hcause]; intro m h; cases h
      · refine ⟨?_, ?_⟩
        · intro _; rw [hlead]; exact (nodeId_ne_zero n).symm
        · intro h; rw [hrole] at h; exact absurd rfl h
  · intro G hG
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro l hl; cases hl
    · intro v hv; cases hv
    · intro n; exact ⟨[], hG, rep3_get _ n⟩
    · intro p hp; cases hp
    · exact ⟨0, Nat.zero_le _, rfl⟩
    · intro p hp; cases hp
    · intro m hm; cases hm

end init

end AntSim
end EtcdGrove
end Perennial

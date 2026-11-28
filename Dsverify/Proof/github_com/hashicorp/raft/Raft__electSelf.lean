/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/Raft__electSelf.lean (241f27e).
-/
/-
The proof of `raft.(*Raft).electSelf`: the election of term `s.term + 1`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.Raft__electSelf
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__getRPCHeader
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__setCurrentTerm
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__persistVote
public import Dsverify.Spec.github_com.hashicorp.raft.raftState__getCurrentTerm
public import Dsverify.Spec.github_com.hashicorp.raft.raftState__getLastEntry
public import Dsverify.Spec.github_com.hashicorp.raft.raftState__goFunc
public import Dsverify.Proof.github_com.hashicorp.raft.handlers.Elect

@[expose] public section

set_option linter.deprecated false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.Assumptions]
variable [hRB : ReceiptBoundLe GF (2 ^ 62)]

open github_com.hashicorp.raft proto gprot

theorem nodup_getElem_not_mem_take {α} {l : List α} {k : Nat} {x : α} (hnd : l.Nodup)
    (h : l[k]? = some x) : x ∉ l.take k := by
  intro hm
  have h1 : x ∈ l.drop k := by
    rw [List.mem_iff_getElem?]; exact ⟨0, by rw [List.getElem?_drop]; simpa using h⟩
  rw [← List.take_append_drop k l, List.nodup_append] at hnd
  exact hnd.2.2 x hm x h1 rfl

theorem mem_take_succ {α} {l : List α} {k : Nat} {x j : α} (h : l[k]? = some x) :
    j ∈ l.take (k + 1) ↔ j ∈ l.take k ∨ j = x := by
  rw [List.take_add_one, h]; simp

theorem start_bag_make {V : Type} [Pos.Countable V] [ZeroVal V] [TypedPointsto (GF := GF) V]
    (P : V → IProp GF) (cap : w64) (ch : Loc) (γc : ChanNames) :
    ⊢ isChan ch γc V -∗ ownChan γc V (if cap = W64 0 then ChanState.Idle else ChanState.Buffered [])
      ={⊤}=∗ isChanBag γc ch P := by
  by_cases h : cap = W64 0
  · rw [if_pos h]; exact start_bag P _ ch γc trivial
  · rw [if_neg h]; exact start_bag P _ ch γc trivial

theorem github_com.hashicorp.raft.Raft.electSelf.wp_proof
    (wp_getCurrentTerm : github_com.hashicorp.raft.raftState.getCurrentTerm.spec (GF := GF) (hG := hG))
    (wp_setCurrentTerm : github_com.hashicorp.raft.Raft.setCurrentTerm.spec (GF := GF) (hG := hG))
    (wp_getLastEntry : github_com.hashicorp.raft.raftState.getLastEntry.spec (GF := GF) (hG := hG))
    (wp_getRPCHeader : github_com.hashicorp.raft.Raft.getRPCHeader.spec (GF := GF) (hG := hG))
    (wp_goFunc : github_com.hashicorp.raft.raftState.goFunc.spec (GF := GF) (hG := hG))
    (wp_persistVote : github_com.hashicorp.raft.Raft.persistVote.spec (GF := GF) (hG := hG))
    (wp_BoolLoad : sync.atomic.Bool.Load.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.Raft.electSelf.spec (GF := GF) (hG := hG) := by
  sorry -- hraft_robust L0: re-proved by its stage (HANDOFF.md)

end proof

end Perennial

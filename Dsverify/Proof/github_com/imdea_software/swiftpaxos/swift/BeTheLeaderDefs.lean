/-
The definitions, specs and lemmas of `BeTheLeader.lean` that its proofs do not need (split out for the import tiers, CLAUDE.md "Import tiers": its importers that are not linking modules import this module, and see no proof).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.AnyFlag
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.QuorumArithDefs

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section spec
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF]

/-- `r.BeTheLeader(args, reply)` (see the file header): no error, a reply `btlOk` admits. -/
abbrev swift.Replica.BeTheLeader.spec : Prop :=
  ∀ (r : Loc) (γc γm : GName) (args reply : Loc) (rv : replica.defs.BeTheLeaderReply),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ∗
      swift.rcvrRes r γc γm ∗ reply ↦ rv }}
    (App (App (Val (r @!! go.GoType.PointerType swift.Replica.ty @!! go!"BeTheLeader"))
      (Val #args)) (Val #reply))
  {{ RET #(interface.nil : GoInterface); ∃ (ld nl : w32),
      reply ↦ replica.defs.BeTheLeaderReply.mk ld nl ∗
      ∃ N fr l, sp.cfg γc γm N fr l ∗ ⌜sp.btlOk N ld nl⌝ }}

end spec

section proof
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF]
variable [swift.Assumptions] [replica.Assumptions] [github_com.orcaman.concurrent_map.Assumptions]
  [sync.Assumptions] [sync.atomic.Assumptions]

/-- Go's `b % N` of a non-negative ballot is in `[0, N)`. -/
theorem swift.srem_nonneg (b : w32) (N : Nat) (hN : 1 ≤ N ∧ N ≤ 7) (hb : 0 ≤ sint.Z b) :
    0 ≤ sint.Z (BitVec.srem b (W32 (sint.Z (W64 (N : Int))))) ∧
      sint.Z (BitVec.srem b (W32 (sint.Z (W64 (N : Int))))) < N := by
  have hN' : sint.Z (W64 (N : Int)) = N := by word
  rw [hN', replica.quorum.leader_val b N (by omega) hb]
  exact ⟨Int.emod_nonneg _ (by omega), Int.emod_lt_of_pos _ (by omega)⟩

/-- The leader of ballot `-1` (`BallotAt(1)` without a quorum file): `-1`, or `0` for `N = 1`. -/
theorem swift.srem_m1 (N : Nat) (h : 1 ≤ N ∧ N ≤ 7) :
    BitVec.srem (W32 (-1)) (W32 (sint.Z (W64 (N : Int)))) = W32 (-1) ∨
      BitVec.srem (W32 (-1)) (W32 (sint.Z (W64 (N : Int)))) = W32 0 := by
  obtain ⟨h1, h2⟩ := h
  have : N = 1 ∨ N = 2 ∨ N = 3 ∨ N = 4 ∨ N = 5 ∨ N = 6 ∨ N = 7 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- `btlOk` of the answers. -/
theorem swift.btlOk_of (N : Nat) (_hN : 1 ≤ N ∧ N ≤ 7) (ld nl : w32)
    (hld : ld = W32 (-2) ∨ (1 ≤ sint.Z ld ∧ sint.Z ld < N))
    (hnl : nl = W32 (-2) ∨ nl = W32 (-1)) : sp.btlOk N ld nl := by
  unfold sp.btlOk
  refine ⟨?_, ?_⟩
  · rcases hld with h | h
    · exact Or.inl h
    · exact Or.inr h
  · rcases hnl with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)

end proof

end Perennial.github_com.imdea_software.swiftpaxos

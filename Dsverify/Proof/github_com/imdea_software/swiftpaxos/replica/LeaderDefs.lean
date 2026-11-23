/-
The definitions, specs and lemmas of `Leader.lean` that its proofs do not need (split out for the import tiers, CLAUDE.md "Import tiers": its importers that are not linking modules import this module, and see no proof).
-/
module

public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.client.Defs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

namespace replica.leader

section proof
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF]
variable [replica.Assumptions]

/-- `Leader(b, N)` for `1 ≤ N < 2^31`. -/
abbrev Leader.specI : Prop :=
  ∀ (b : w32) (N : Nat),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.replica ∗
      ⌜1 ≤ N ∧ N < 2 ^ 31⌝ }}
    (App (App (Val (@! replica.Leader)) (Val #b)) (Val #(W64 N)))
  {{ (r : w32), RET #r; ⌜0 ≤ b.toInt → ∀ k : w32, 0 ≤ k.toInt →
      (k = r ↔ sp.rid k = sp.leaderOf N (sp.bal b))⌝ }}

omit [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [replica.Assumptions] in
theorem srem_leader (b : w32) (N : Nat) (hN : 1 ≤ N ∧ N < 2 ^ 31) (hb : 0 ≤ b.toInt) (k : w32)
    (hk : 0 ≤ k.toInt) :
    k = BitVec.srem b (W32 (sint.Z (W64 (N : Int)))) ↔ sp.rid k = sp.leaderOf N (sp.bal b) := by
  have hn : W32 (sint.Z (W64 (N : Int))) = BitVec.ofNat 32 N := by
    apply BitVec.eq_of_toNat_eq
    have h1 : sint.Z (W64 (N : Int)) = N := by word
    rw [h1]; simp [W32]
  rw [hn]
  have hmb : b.msb = false := by rw [BitVec.msb_eq_toInt]; simp; omega
  have hmn : (BitVec.ofNat 32 N).msb = false := by
    rw [BitVec.msb_eq_toNat]; simp; omega
  have hmk : k.msb = false := by rw [BitVec.msb_eq_toInt]; simp; omega
  rw [BitVec.srem_eq, hmb, hmn]
  simp only
  have hbn := BitVec.toInt_eq_toNat_of_msb hmb
  have hkn := BitVec.toInt_eq_toNat_of_msb hmk
  unfold sp.rid sp.bal sp.leaderOf
  rw [hbn, hkn]
  simp only [Int.toNat_natCast]
  have hNm : N % 4294967296 = N := Nat.mod_eq_of_lt (by omega)
  constructor
  · intro h; subst h; rw [BitVec.toNat_umod]; simp [hNm]
  · intro h; apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_umod, h]; simp [hNm]

end proof

end replica.leader

end Perennial.github_com.imdea_software.swiftpaxos

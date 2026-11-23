/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/AqQuorum.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
The fast quorum `qs.AQ(b)` as a message-set quorum (round 23, sv-swb; D18 G2): `AQ`'s result
(`qOwn … (aqOf N b)`) stored as a `QuorumI` is `quorumIs` with its members in the model's
`sp.AQ N b` (what `swift.fqShare` holds; `New` and `handleSync` set `FQ = qs.AQ(ballot)`).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.QuorumModel
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.MsgSetQ
public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.swift.Inv
import all Dsverify.Spec.github_com.imdea_software.swiftpaxos.swift.Inv

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section defs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics]

/-- `fq` is a fast quorum of ballot `b` (of `N` replicas): a message-set quorum whose members
are in the model's `sp.AQ N b` (persistent); round 35 (table E7, plan R.4.1, D7): `b`'s leader
is a member. -/
def swift.fqOk (fq : GoInterface) (N b : Nat) : IProp netDistGF :=
  iprop(∃ (szF : Nat) (memF : w32 → Prop), replica.mset.quorumIs fq szF memF ∗
    ⌜(∀ i : w32, memF i → sp.rid i ∈ sp.AQ N b) ∧
      (∀ i : w32, 0 ≤ sint.Z i → sp.rid i = sp.leaderOf N b → memF i)⌝)

instance swift.fqOk_persistent (fq : GoInterface) (N b : Nat) :
    Persistent (swift.fqOk fq N b) := by unfold swift.fqOk; infer_instance

end defs

section lemmas
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics]

theorem swift.rid_w32n (x : Nat) (hx : x < 2 ^ 31) : sp.rid (replica.quorum.w32n x) = x := by
  unfold sp.rid replica.quorum.w32n
  have h : (W32 (x : Int)).toInt = (x : Int) := by
    simp only [W32]; rw [BitVec.toInt_ofInt]
    exact Int.bmod_eq_of_le (by omega) (by omega)
  rw [h]; simp

theorem swift.aq_quorumIs (N b : Nat) (hN : 1 ≤ N ∧ N ≤ 7) (q : Loc) :
    replica.quorum.qOwn q DFrac.discard (replica.quorum.aqOf N b) ⊢
      replica.mset.quorumIs (interface.mkOk replica.Quorum.ty #q) (replica.quorum.aqOf N b).length
        (fun k => k ∈ (replica.quorum.aqOf N b).map replica.quorum.w32n) ∗
      ⌜∀ i : w32, i ∈ (replica.quorum.aqOf N b).map replica.quorum.w32n → sp.rid i ∈ sp.AQ N b⌝ := by
  iintro #H
  obtain ⟨hlen, hnd, hlt, -⟩ := replica.quorum.aqOf_ok N b hN
  isplitl
  · iunfold replica.mset.quorumIs
    isplitr
    · ipureintro; rw [hlen]; omega
    iright
    iexists q, replica.quorum.aqOf N b
    iframe H
    ipureintro
    exact ⟨rfl, rfl, hnd, fun x hx => by have := hlt x hx; omega, fun k => Iff.rfl⟩
  · ipureintro
    intro i hi
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hi
    rw [← replica.quorum.aqOf_eq_AQ, swift.rid_w32n x (by have := hlt x hx; omega)]
    exact hx

theorem swift.w32n_rid (i : w32) (h : 0 ≤ sint.Z i) : replica.quorum.w32n (sp.rid i) = i := by
  unfold replica.quorum.w32n sp.rid
  have h' : (0 : Int) ≤ i.toInt := h
  rw [Int.toNat_of_nonneg h']
  simp [W32]

/-- E7 for `AQ` (round 35): `b`'s leader is in `aqOf N b`. -/
theorem swift.aq_leader (N b : Nat) (hN : 1 ≤ N) (i : w32) (h0 : 0 ≤ sint.Z i)
    (hl : sp.rid i = sp.leaderOf N b) :
    i ∈ (replica.quorum.aqOf N b).map replica.quorum.w32n := by
  rw [← swift.w32n_rid i h0, replica.quorum.aqOf_eq_AQ]
  exact List.mem_map_of_mem (hl ▸ (sp.AQ_majority N b (by omega)).2)

theorem swift.aq_fqOk (N b : Nat) (hN : 1 ≤ N ∧ N ≤ 7) (q : Loc) :
    replica.quorum.qOwn q DFrac.discard (replica.quorum.aqOf N b) ⊢
      swift.fqOk (interface.mkOk replica.Quorum.ty #q) N b := by
  iintro #H
  ihave ⟨#Hq, %Hm⟩ := swift.aq_quorumIs N b hN q $$ H
  iunfold swift.fqOk
  iexists _, _
  iframe Hq
  ipureintro; exact ⟨Hm, fun i h0 hl => swift.aq_leader N b hN.1 i h0 hl⟩

end lemmas

end Perennial.github_com.imdea_software.swiftpaxos

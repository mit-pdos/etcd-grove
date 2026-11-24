/-
The definitions, specs and lemmas of `HandleAcks.lean` that its proofs do not need (split out for the import tiers, CLAUDE.md "Import tiers": its importers that are not linking modules import this module, and see no proof).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.pkg.TimeInit
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.client.HandlerState
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.client.BufferClient__RegisterReplyDefs
public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.dlog.Logger__Println

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

namespace swift.handler

section proof
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps]
variable [swift.Assumptions] [client.Assumptions] [time.Assumptions] [dlog.Assumptions]

omit [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps] [swift.Assumptions] [client.Assumptions] [time.Assumptions]
  [dlog.Assumptions] in
/-- A command not delivered, of the client, has no delivery token yet. -/
theorem fresh_seq (H : HC) (D : GMap swift.CommandId Unit) (Dn : GMap Nat Unit)
    (x : swift.CommandId)
    (hD : ∀ x, D.lookup x = some () → x.ClientId' = H.cid ∧ 0 ≤ x.SeqNum'.toInt)
    (hDn : ∀ n, (Dn.lookup n).isSome ↔ ∃ x, D.lookup x = some () ∧ x.SeqNum'.toNat = n)
    (hx : D.lookup x = none) (hc : (cmdOf x).cl = H.cid) : Dn.lookup x.SeqNum'.toNat = none := by
  cases h : Dn.lookup x.SeqNum'.toNat with
  | none => rfl
  | some u =>
    exfalso
    obtain ⟨x', h1, h2⟩ := (hDn _).mp (by rw [h]; rfl)
    obtain ⟨c', -⟩ := hD x' h1
    have : x' = x := by
      cases x'; cases x
      simp only [cmdOf] at hc
      simp only at c' h2
      simp only [swift.CommandId.mk.injEq]
      exact ⟨c'.trans hc.symm, BitVec.eq_of_toNat_eq h2⟩
    rw [this, hx] at h1; cases h1

/-- The internal spec of `c.handleFastAndSlowAcks(leaderMsg, msgs)` as `x`'s fast or slow
message set calls it. -/
abbrev handleFastAndSlowAcks.specI : Prop :=
  ∀ (H : HC) (fast : Bool) (x : sp.CmdId) (lm : GoInterface) (sl : GoSlice)
    (ms : List GoInterface),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ∗
      ctxOk H ∗ core H ∗ sl ↦* ms ∗
      replica.mset.handlerPre (H.N / 2 + 1) (entryP H.γ H.γc H.γm H.N H.cid fast x) accA
        (leaderP H.γ H.γc H.γm H.γr H.cid fast x) lm ms }}
    (App (App (Val (H.c @!! go.GoType.PointerType swift.Client.ty @!! go!"handleFastAndSlowAcks"))
      (Val #lm)) (Val #sl))
  {{ RET #(); core H }}

end proof

end swift.handler

end Perennial.github_com.imdea_software.swiftpaxos

/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/BatcherFast.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
The batcher's fast-ack senders (round 14; `handlePropose`'s fast ack): `b.SendFastAck(l)` and
`b.SendFastAckClient(l, cid)` (batcher.go) put an operation with `batchFastP` on the batcher's
fast-ack channel.

* `swift.fastOpP γ γc γm rp l cl`: `batchFastP` but the operation: the sending context, the
  owned `*MFastAck` (freed by the batcher), its model ack sent by this replica with its witness,
  well formed and not shaped as a slow ack, and for a client copy (`cl`) `facClientOk`.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.NewSpecs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section specs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF]
variable [swift.Assumptions]

/-- What a fast ack sent through the batcher needs (see the file header). -/
def swift.fastOpP (γ : sp.Names) (γc γm : GName) (rp l : Loc) (cl : Bool) : IProp netDistGF :=
  iprop(∃ (N : Nat) (me : w32) (fa : swift.MFastAck) (f : sp.FastAck),
    swift.sendCtxN γ γc γm rp N me ∗ l ↦ fa ∗ swift.fastAckRepr fa f ∗ sp.fastAckOk γ f ∗
    ⌜f.rep = me ∧ f.wf ∧ f.dep ≠ [f.id] ∧ f.cs.length + 1 < 2 ^ 62⌝ ∗
    (if cl then swift.facClientOk γ γc γm f else True))

/-- `b.SendFastAck(l)`. -/
abbrev swift.Batcher.SendFastAck.specI : Prop :=
  ∀ (γ : sp.Names) (γc γm : GName) (rp b l : Loc),
  {{ swift.batcherH γ γc γm rp b ∗ swift.fastOpP γ γc γm rp l false }}
    (App (Val (b @!! go.GoType.PointerType swift.Batcher.ty @!! go!"SendFastAck")) (Val #l))
  {{ RET #(); True }}

/-- `b.SendFastAckClient(l, cid)`. -/
abbrev swift.Batcher.SendFastAckClient.specI : Prop :=
  ∀ (γ : sp.Names) (γc γm : GName) (rp b l : Loc) (cid : w32),
  {{ swift.batcherH γ γc γm rp b ∗ swift.fastOpP γ γc γm rp l true }}
    (App (App (Val (b @!! go.GoType.PointerType swift.Batcher.ty @!! go!"SendFastAckClient"))
      (Val #l)) (Val #cid))
  {{ RET #(); True }}

end specs

section proofs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF]
variable [swift.Assumptions]

theorem swift.Batcher.SendFastAck.wp_proof : swift.Batcher.SendFastAck.specI (hG := hG) := by
  intro γ γc γm rp b l
  wp_start as ⟨#Hb, Hop⟩
  iunfold swift.batcherH at Hb
  icases Hb with ⟨%fa, %ls, %γ1, %γ2, #Hbs, #Hfa, #Hls⟩
  ihave #Hbs2 := Hbs
  iStructNamedPrefix Hbs2 "B"
  wp_auto
  wp_apply wp_bag_send (t := swift.BatcherOp.ty) γ1 fa _ (swift.batchFastP γ γc γm rp) $$ [Hop]
  · iframe Hfa
    iunfold swift.fastOpP at Hop
    icases Hop with ⟨%N, %me, %fa', %f, #Hc, Hl, #Hr, #Hok, %Hf, Hcl⟩
    iunfold swift.batchFastP
    iexists N, me, l, fa', f
    iframe Hc Hl Hr Hok
    isplitr
    · ipureintro; rfl
    isplitr
    · ipureintro; exact Hf
    simp only [Bool.false_eq_true, ↓reduceIte]
    itrivial
  iapply HΦ; itrivial

theorem swift.Batcher.SendFastAckClient.wp_proof :
    swift.Batcher.SendFastAckClient.specI (hG := hG) := by
  intro γ γc γm rp b l cid
  wp_start as ⟨#Hb, Hop⟩
  iunfold swift.batcherH at Hb
  icases Hb with ⟨%fa, %ls, %γ1, %γ2, #Hbs, #Hfa, #Hls⟩
  ihave #Hbs2 := Hbs
  iStructNamedPrefix Hbs2 "B"
  wp_auto
  wp_apply wp_bag_send (t := swift.BatcherOp.ty) γ1 fa _ (swift.batchFastP γ γc γm rp) $$ [Hop]
  · iframe Hfa
    iunfold swift.fastOpP at Hop
    icases Hop with ⟨%N, %me, %fa', %f, #Hc, Hl, #Hr, #Hok, %Hf, Hcl⟩
    iunfold swift.batchFastP
    iexists N, me, l, fa', f
    iframe Hc Hl Hr Hok
    isplitr
    · ipureintro; rfl
    isplitr
    · ipureintro; exact Hf
    iexact Hcl
  iapply HΦ; itrivial

end proofs

end Perennial.github_com.imdea_software.swiftpaxos

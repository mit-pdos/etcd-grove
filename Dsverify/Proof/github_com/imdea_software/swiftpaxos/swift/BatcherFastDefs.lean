/-
The definitions, specs and lemmas of `BatcherFast.lean` that its proofs do not need (split out for the import tiers, CLAUDE.md "Import tiers": its importers that are not linking modules import this module, and see no proof).
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
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps]
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
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps]
variable [swift.Assumptions]

end proofs

end Perennial.github_com.imdea_software.swiftpaxos

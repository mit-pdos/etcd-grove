/-
The definitions, specs and lemmas of `BufferClient__RegisterReply.lean` that its proofs do not need (split out for the import tiers, CLAUDE.md "Import tiers": its importers that are not linking modules import this module, and see no proof).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.client.Defs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Perennial.Proof.time

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section proof
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF]
variable [client.Assumptions] [time.Assumptions]

/-- The internal spec of `RegisterReply`. -/
abbrev client.BufferClient.RegisterReply.specI : Prop :=
  ∀ (b : Loc) (bv : client.BufferClient) (γ : sp.Names) (cid : w32) (γd : GName)
    (γch : ChanNames) (vsl : GoSlice) (bs : List w8) (seq : w32),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.time ∗
      b ↦□ bv ∗ isChanBag γch bv.Reply' (client.replyP γ cid γd) ∗ vsl ↦*□ bs ∗
      sp.doneRes γ ⟨cid, seq⟩ bs ∗
      ghostMapElem (K := Nat) (V := Unit) γd seq.toNat (DFrac.own 1) () ∗ ⌜0 ≤ seq.toInt⌝ }}
    (App (App (Val (b @!! go.GoType.PointerType client.BufferClient.ty @!! go!"RegisterReply"))
      (Val #vsl)) (Val #seq))
  {{ RET #(); True }}

end proof

end Perennial.github_com.imdea_software.swiftpaxos

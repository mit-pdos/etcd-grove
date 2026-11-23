/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/client/BufferClient__RegisterReply.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`RegisterReply(val, seqnum)` (the handler's hand-off to `Write`/`Read`): a decided result of the
client's command `seqnum` (non-negative), with its delivery token, sent on `Reply` as `replyPI`.
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
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF]
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

theorem client.BufferClient.RegisterReply.wp_proof :
    client.BufferClient.RegisterReply.specI (hG := hG) := by
  intro b bv γ cid γd γch vsl bs seq
  wp_start as ⟨#Hb, #Hbag, #Hv, #Hdone, Htok, %Hseq⟩
  ihave #Hbf := Hb
  iStructNamed Hbf
  wp_auto
  wp_apply time.wp_Now $$ [$Hpkg] as %tm -
  ipersist «$v»
  wp_apply wp_bag_send γch bv.Reply' «$v_ptr» (client.replyP γ cid γd) $$ [Htok]
  · iframe #
    iapply (client.replyP_unfold _ _ _ _).2
    iexists _, bs, seq.toNat
    iframe «$v» Hv
    have hn : seq.toNat < 2 ^ 31 := by word
    isplitr
    · ipureintro
      refine ⟨?_, hn⟩
      dsimp only; word
    have hw : (⟨cid, W32 (seq.toNat : Int)⟩ : sp.CmdId) = ⟨cid, seq⟩ := by
      congr 1; word
    rw [hw]
    iframe #
    iframe
  iapply HΦ; itrivial

end proof

end Perennial.github_com.imdea_software.swiftpaxos

/-
Package `proxy`: sending answers (`sendMessage`, `sendClientResponse`).
-/
module

public import Dsverify.Proof.raxos.Proxy.Defs

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Perennial.raxos


open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open Perennial.raxos.pure Perennial.raxos.msg
open raxos.replica.src

section proofs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [π : NetProtoGS] [qv : hyp.QpVocab GF]
variable [raxos.replica.src.Assumptions] [raxos.proto.client.Assumptions]

theorem wp_sendMessage (γ : QNames) (pr och : Loc) (γo : ChanNames) (peer : w64)
    (rp : raxos.common.RPCPair) (l : Loc) (c : Nat) (x r : GoString) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.raxos.replica.src ∗
        pr.[Proxy, go!"outgoingMessageChan"] ↦□ och ∗ isChanBag γo och (outP γ) ∗
        ⌜rp.Code' = W8 1 ∧ rp.Obj' = interface.mkOk (go.GoType.PointerType raxos.proto.client.ClientBatch.ty) #l ∧
          c < 6 ∧ sint.Z peer = clientName c⌝ ∗
        repCB l .discard ⟨x, clientName c, [r]⟩ ∗ opAns γ x r }}
      (App (App (Val (pr @!! go.GoType.PointerType Proxy.ty @!! go!"sendMessage")) (Val #peer)) (Val #rp))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hoch, #Hbag, %Hrp, #Hrep, #Hans⟩
  wp_auto
  ipersist rpcPair
  wp_apply wp_bag_send $$ [Hbag]
  · iframe Hbag
    iunfold outP
    iexists rp, l, c, x, r
    dsimp only
    iframe rpcPair Hrep Hans
    ipureintro; exact Hrp
  wp_end

/-- An executed batch's result, as `sendClientResponse` needs it: the `"nil"` batch's (sender
`-1`, not sent) or an answer to client `c`'s request. -/
def ansP (γ : QNames) (o : raxos.proto.client.ClientBatch) : IProp GF :=
  iprop(⌜sint.Z o.Sender' = -1⌝ ∨
    ∃ c x r, repCBVal o .discard ⟨x, clientName c, [r]⟩ ∗ opAns γ x r ∗ ⌜c < 6⌝)

instance ansP_persistent (γ : QNames) (o : raxos.proto.client.ClientBatch) :
    Persistent (ansP (GF := GF) γ o) := by
  unfold ansP; infer_instance

theorem wp_sendClientResponse (γ : QNames) (pr och : Loc) (γo : ChanNames) (rs : GoSlice)
    (outs : List raxos.proto.client.ClientBatch) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.raxos.replica.src ∗
        pr.[Proxy, go!"outgoingMessageChan"] ↦□ och ∗ isChanBag γo och (outP γ) ∗
        pr.[Proxy, go!"clientBatchRpc"] ↦□ W8 1 ∗
        ⌜outs.length = sint.nat rs.len ∧ 0 ≤ sint.Z rs.len⌝ ∗
        ([∗list] k ↦ o ∈ outs, ptCB (sliceIndexRef raxos.proto.client.ClientBatch (k : Int) rs) .discard o) ∗
        [∗list] o ∈ outs, ansP γ o }}
      (App (Val (pr @!! go.GoType.PointerType Proxy.ty @!! go!"sendClientResponse")) (Val #rs))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hoch, #Hbag, #Hcode, %Hrslen, #Hrs, #Hans⟩
  wp_auto
  ihave HI : (∃ i : w64, "i" ∷ i_ptr ↦ i ∗ "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z rs.len⌝ : IProp GF)
      $$ [i]
  · iexists W64 0; iframe; ipureintro; exact ⟨by word, by word⟩
  wp_for HI
  wp_if_destruct
  · have Hilt : sint.nat i < outs.length := by word
    list_elem outs (sint.nat i) as o
    have Hb : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z rs.len := ⟨Hi.1, Hif⟩
    ihave #Hel : ptCB (GF := GF) (sliceIndexRef raxos.proto.client.ClientBatch (sint.Z i) rs) .discard o
        $$ [Hrs]
    · rw [show sint.Z i = ((sint.nat i : Nat) : Int) by word]
      iapply (BigSepL.bigSepL_lookup (Φ := fun k y =>
        ptCB (GF := GF) (sliceIndexRef raxos.proto.client.ClientBatch (k : Int) rs) .discard y)
        Ho_lookup) $$ Hrs
    ihave #Ho := BigSepL.bigSepL_lookup (Φ := fun _ y => ansP (GF := GF) γ y) Ho_lookup $$ Hans
    repeat' (first | wp_auto | simp only [Hb, _root_.and_self, ↓reduceIte])
    wp_if_destruct
    · wp_for_post
      iframe
      iexists i + W64 1; iframe; ipureintro; exact ⟨by word, by word⟩
    · iunfold ansP at Ho
      icases Ho with (%Hm1 | ⟨%cl, %x, %r, #Hov, #Hop, %Hok⟩)
      · exfalso; apply Hif; word
      repeat' (first | wp_auto | simp only [Hb, _root_.and_self, ↓reduceIte])
      wp_apply wp_sendMessage γ pr och γo _ _ (sliceIndexRef raxos.proto.client.ClientBatch (sint.Z i) rs) cl x r
        $$ [Hbag Hoch Hel Hov Hop]
      · iframe Hbag Hoch Hop
        isplitr
        · iunfold repCBVal at Hov
          icases Hov with ⟨%ps, %Hsx, -⟩
          ipureintro; exact ⟨rfl, rfl, Hok, Hsx.1⟩
        iunfold repCB
        iexists o
        iframe Hel Hov
      wp_for_post
      iframe
      iexists i + W64 1; iframe; ipureintro; exact ⟨by word, by word⟩
  · wp_end

end proofs
end Perennial.raxos

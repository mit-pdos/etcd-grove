/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/H2a/Reply.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

# Unit H2a: the sends of `handlePreAccept` (`replyPreAccept`, the `PreAcceptOK` send)
-/
module

public import Dsverify.Proof.gryff.H2.Env
public import Dsverify.GeneratedProof.gryff.examples.gryffnet

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.replica2

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net proto
open Perennial.gryff.model (RState Copy LB Proposal Msg Ev Out Cmd Deps)
open Perennial.gryff.replica (XS rowOwn nSlots)

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- A send to a peer is to a replica id other than this one's. -/
theorem sendPeer_some (s : RState) (k : Fin 3) (hid : s.id = rid32 k) (lid : w32) (m : Msg)
    (o : Out) (hs : model.sendPeer s lid m = some o) :
    ∃ d : Fin 3, o = .send d m ∧ lid = rid32 d ∧ d ≠ k := by
  unfold model.sendPeer model.sendTo model.dstOf at hs
  split at hs
  · cases hs
  · rename_i hne
    split at hs
    · rename_i hb
      simp only [Option.map_some, Option.some.injEq] at hs
      refine ⟨⟨(sint.Z lid).toNat, by omega⟩, hs.symm, ?_, ?_⟩
      · simp only [rid32]
        have : (((sint.Z lid).toNat : Nat) : Int) = sint.Z lid := by omega
        rw [this]; simp only [W32]; exact BitVec.ofInt_toInt.symm
      · intro hk
        apply hne
        rw [hid, ← hk]
        simp only [rid32]
        have : (((sint.Z lid).toNat : Nat) : Int) = sint.Z lid := by omega
        rw [this]; simp only [W32]; exact BitVec.ofInt_toInt.symm
    · cases hs

section
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [π : NetProtoGS] [sem : go.Semantics]
variable [gA : examples.gryffnet.Assumptions] [fa : src.fastrpc.Assumptions] [wire.BufioSpecs GF]
variable [binA : wire.BinaryVarintHyps GF] -- H1-R6 / N-1
variable [sortA : Perennial.gryff.replica2.SortSliceHyp GF]
variable [strconvA : strconv.Assumptions] -- N-5


set_option goose.wp.extras true

/-- The `PreAcceptOK` send's fixed fields. -/
theorem h2Fixed_pok (k : Fin 3) (gR h : Loc) :
    h2Fixed (GF := GF) k gR h ⊢ h.[src.gryff.EPaxosRMWHandler, go!"broadcastOptimizationEnabled"] ↦□ false ∗
      ∃ c : w8, h.[src.gryff.EPaxosRMWHandler, go!"preAcceptOKRPC"] ↦□ c ∗
        rpcCodeIs "preAcceptOK" c := by
  iintro H
  unfold h2Fixed
  icases H with ⟨%pS, %alS, %addrs, %st, %cPA, %cA, %cC, %cCS, %cPAR, %cPAO, %cAR, %cEx,
    -, -, -, -, -, -, -, -, -, #HbOE, -, -, -, -, -, -, -, -, -, #HcPAO, #HrcPAO, -⟩
  isplitr
  · iexact HbOE
  iexists cPAO
  isplitr
  · iexact HcPAO
  · iexact HrcPAO

/-- `replyPreAccept(lid, reply)`: the owed `PreAcceptReply` goes to the sender. -/
theorem wp_replyPreAccept_a (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (r gR h : Loc)
    (t : List Ev) (s : RState) (hid : s.id = rid32 k) (lid : w32)
    (g : wire.gryffproto.PreAcceptReply.Msg) (p : Loc) (o : Out) (outs : List Out)
    (hs : model.sendPeer s lid (.preAcceptReply (preAcceptReplyOf g)) = some o) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryff ∗
        h.[src.gryff.EPaxosRMWHandler, go!"R"] ↦□ r ∗ r.[src.gryff.Replica, go!"Replica"] ↦□ gR ∗
        genericOk γ ρ k r gR h ∗ □ h2Fixed k gR h ∗ p ↦ g ∗ pendingOuts γ ρ k r t (o :: outs) }}
      (App (App (Val (h @!! go.GoType.PointerType src.gryff.EPaxosRMWHandler.ty @!!
        go!"replyPreAccept")) (Val #lid)) (Val #p))
    {{ RET #(); pendingOuts γ ρ k r t outs }} := by
  obtain ⟨d, rfl, rfl, hdk⟩ := sendPeer_some s k hid lid _ o hs
  wp_start as ⟨#HR, #HgR, #Hgen, #Hfix, Hp, Hpend⟩
  unfold h2Fixed
  icases Hfix with ⟨%pS, %alS, %addrs, %st, %cPA, %cA, %cC, %cCS, %cPAR, %cPAO, %cAR, %cEx,
    -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, #HcPAR, #HrcPAR, -⟩
  wp_auto
  ihave Hm : msgAt p (.preAcceptReply (preAcceptReplyOf g)) $$ [Hp]
  · unfold msgAt; iexists g; iframe; ipureintro; rfl
  have hsend := Replica.SendMsg.wp γ ρ k d r gR h t (.preAcceptReply (preAcceptReplyOf g)) p cPAR
    outs hdk
  simp only [msgKind, msgTy] at hsend
  wp_method_call
  wp_auto
  wp_apply hsend $$ [$Hgen $HgR $HrcPAR $Hm $Hpend] as ⟨-, Hpend⟩
  wp_end

end

end Perennial.gryff.replica2

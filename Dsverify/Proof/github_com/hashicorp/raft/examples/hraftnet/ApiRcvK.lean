/-
The API's receiver for the world's wrapped spec (`apiSvcK`, `ServerShare.lean`; notes/dsv-hraft.md,
S5d): the receiver laws of the drawn protocol's `apiSvc` give them for `apiSvcK`, to the server, which
knows the draw (`apiRcvLaws_svcK`).
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.ServerShare
public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.CodecApi

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace github_com.hashicorp.raft.examples.hraftnet

section rcv
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : Assumptions]
variable [bvi : go.BasicIntoValInj]
variable [net.rpc.Assumptions] [π : NetProtoGS]
variable [rsem : github_com.hashicorp.raft.Assumptions]

theorem encOf_svcKE {AV : Type} (encA : AV → List w8) (γc : GName) (ok : GoString → List w8 → Prop)
    (Sn : Nat → net.rpc.MethodSpec GF) (M : GoString) (h : ∀ bs, ok M bs → ∃ va, bs = encA va) :
    encOf (GF := GF) encA (svcKE γc ok Sn M) := by
  intro args Φ
  iintro H
  unfold svcKE
  icases H with ⟨%Hok, -⟩
  ipureintro
  exact h args Hok

theorem apiMeth_svcKE {A R AV RV : Type} [TypedPointsto (GF := GF) A] [TypedPointsto (GF := GF) R]
    [ZeroVal R] (P : IProp GF) (s : Loc) (M : GoString) (aOwn : A → DFrac → AV → IProp GF)
    (encA : AV → List w8) (rOwn : R → DFrac → RV → IProp GF) (encR : RV → List w8)
    (γc : GName) (ok : GoString → List w8 → Prop) (Sn : Nat → net.rpc.MethodSpec GF) (n : Nat)
    (h : apiMeth.spec (GF := GF) P s M aOwn encA rOwn encR (Sn n M)) :
    apiMeth.spec (GF := GF) iprop(P ∗ chosen γc n) s M aOwn encA rOwn encR (svcKE γc ok Sn M) := by
  intro ap rp wa va Φ
  iintro %Ψ ⟨⟨HP, #Hc⟩, %Hl, HS, Ha, Hown, Hr⟩ HΨ
  iapply fupd_wp
  imod svcKE_elim γc ok Sn n M (encA va) Φ $$ [HS] with HS
  · iframe Hc HS
  imodintro
  iapply (h ap rp wa va Φ) $$ [HP HS Ha Hown Hr] HΨ
  iframe
  ipureintro; exact Hl

/-- **The API's receiver laws for the world's wrapped spec**, to who knows the draw `n`. -/
theorem apiRcvLaws_svcK (P : IProp GF) (s : Loc) (K : HK GF) (n : Nat)
    (L : ApiRcvLaws (GF := GF) P s (apiSvc (K.γs n) (K.fcs n))) :
    ApiRcvLaws (GF := GF) iprop(P ∗ chosen K.γc n) s (apiSvcK K) where
  enc_AddNonvoter := encOf_svcKE _ _ _ _ _ (fun _ h => h.2.2 (by simp))
  meth_AddNonvoter := apiMeth_svcKE P s _ _ _ _ _ _ _ _ n L.meth_AddNonvoter
  enc_AddVoter := encOf_svcKE _ _ _ _ _ (fun _ h => h.2.2 (by simp))
  meth_AddVoter := apiMeth_svcKE P s _ _ _ _ _ _ _ _ n L.meth_AddVoter
  enc_Apply := encOf_svcKE _ _ _ _ _ (fun _ h => h.1 rfl)
  meth_Apply := apiMeth_svcKE P s _ _ _ _ _ _ _ _ n L.meth_Apply
  enc_DemoteVoter := encOf_svcKE _ _ _ _ _ (fun _ h => h.2.2 (by simp))
  meth_DemoteVoter := apiMeth_svcKE P s _ _ _ _ _ _ _ _ n L.meth_DemoteVoter
  enc_LeadershipTransfer := encOf_svcKE _ _ _ _ _ (fun _ h => h.2.2 (by simp))
  meth_LeadershipTransfer := apiMeth_svcKE P s _ _ _ _ _ _ _ _ n L.meth_LeadershipTransfer
  enc_Read := encOf_svcKE _ _ _ _ _ (fun _ h => h.2.1 rfl)
  meth_Read := apiMeth_svcKE P s _ _ _ _ _ _ _ _ n L.meth_Read
  enc_RemoveServer := encOf_svcKE _ _ _ _ _ (fun _ h => h.2.2 (by simp))
  meth_RemoveServer := apiMeth_svcKE P s _ _ _ _ _ _ _ _ n L.meth_RemoveServer
  enc_Snapshot := encOf_svcKE _ _ _ _ _ (fun _ h => h.2.2 (by simp))
  meth_Snapshot := apiMeth_svcKE P s _ _ _ _ _ _ _ _ n L.meth_Snapshot
  enc_Status := encOf_svcKE _ _ _ _ _ (fun _ h => h.2.2 (by simp))
  meth_Status := apiMeth_svcKE P s _ _ _ _ _ _ _ _ n L.meth_Status

end rcv

end github_com.hashicorp.raft.examples.hraftnet

end Perennial

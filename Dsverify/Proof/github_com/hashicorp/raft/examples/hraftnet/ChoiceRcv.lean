/-
The hraft kit's wrapped rpc world (`Choice.lean`) for the transport: who knows the draw serves raft
addresses under the wrapped spec (`svcAt_svcK`), and the receiver laws of the drawn protocol's
`raftSvc` give them for the wrapped spec (`raftRcvLaws_svcK`; notes/dsv-hraft.md, S5d).
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.Choice
public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.CodecRcvSvc

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace github_com.hashicorp.raft.examples.hraftnet

section choiceTrans
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [π : NetProtoGS] [rsem : github_com.hashicorp.raft.Assumptions]

/-- A transport's view of a wrapped world (`svcAt`, `rpctransport/Trans.lean`): who knows the draw `n`
serves raft address `a`'s receiver of protocol `Sn n`'s. -/
theorem svcAt_svcK (γc : GName) (Sn : Nat → net.rpc.MethodSpec GF) (n : Nat)
    (γ : gprot.GNames) (snapP : Nat → List w8 → IProp GF) (W : net.rpc.RpcWorld GF) (a na : GoString)
    (hW : W.SS na rpctransport.svcName = some (svcK γc Sn))
    (hS : Sn n = rpctransport.raftSvc γ snapP a) :
    chosen (GF := GF) γc n ⊢ rpctransport.svcAt γ snapP W a na := by
  iintro #Hc
  unfold rpctransport.svcAt
  iexists svcK γc Sn
  isplitr; · ipureintro; exact hW
  imodintro
  iintro %M %bs %Φ H
  iapply svcK_intro γc Sn n
  iframe Hc
  rw [hS]
  iexact H

end choiceTrans

section rcv
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : Assumptions]
variable [bvi : go.BasicIntoValInj]
variable [net.rpc.Assumptions] [π : NetProtoGS]

/-- A method spec's deposits are encodings for the wrapped spec if they are for every size's. -/
theorem encOf_svcK {AV : Type} (encA : AV → List w8) (γc : GName) (Sn : Nat → net.rpc.MethodSpec GF)
    (M : GoString) (h : ∀ n, encOf (GF := GF) encA (Sn n M)) :
    encOf (GF := GF) encA (svcK γc Sn M) := by
  intro args Φ
  iintro H
  unfold svcK
  icases H with ⟨%n, -, H⟩
  iapply (h n args Φ) $$ H

/-- A method obligation for the drawn size's spec gives it for the wrapped spec, to who knows the
draw. -/
theorem rpcMeth_svcK {A R AV RV : Type} [TypedPointsto (GF := GF) A] [TypedPointsto (GF := GF) R]
    [ZeroVal R] (P : IProp GF) (s : Loc) (M : GoString) (aOwn : A → DFrac → AV → IProp GF)
    (encA : AV → List w8) (rOwn : R → DFrac → RV → IProp GF) (encR : RV → List w8)
    (γc : GName) (Sn : Nat → net.rpc.MethodSpec GF) (n : Nat)
    (h : rpcMeth.spec (GF := GF) P s M aOwn encA rOwn encR (Sn n M)) :
    rpcMeth.spec (GF := GF) iprop(P ∗ chosen γc n) s M aOwn encA rOwn encR (svcK γc Sn M) := by
  intro ap rp wa va Φ
  iintro %Ψ ⟨⟨HP, #Hc⟩, %Hl, HS, Ha, Hown, Hr⟩ HΨ
  ihave HS := svcK_elim γc Sn n M (encA va) Φ $$ [HS]
  · iframe Hc HS
  iapply (h ap rp wa va Φ) $$ [HP HS Ha Hown Hr] HΨ
  iframe
  ipureintro; exact Hl

/-- **The transport's receiver laws for the wrapped spec**, to who knows the draw `n`: from those of
`Sn n`, each size's spec a `raftSvc` (its deposits encodings). -/
theorem raftRcvLaws_svcK (P : IProp GF) (s : Loc) (γc : GName)
    (γs : Nat → gprot.GNames) (snapPs : Nat → Nat → List w8 → IProp GF) (a : GoString) (n : Nat)
    (L : RaftRcvLaws (GF := GF) P s (rpctransport.raftSvc (γs n) (snapPs n) a)) :
    RaftRcvLaws (GF := GF) iprop(P ∗ chosen γc n) s
      (svcK γc (fun m => rpctransport.raftSvc (γs m) (snapPs m) a)) where
  enc_AppendEntries := encOf_svcK _ γc _ _ (fun m => raftSvc_encOf_AppendEntries (γs m) (snapPs m) a)
  meth_AppendEntries := rpcMeth_svcK P s _ _ _ _ _ γc _ n L.meth_AppendEntries
  enc_InstallSnapshot := encOf_svcK _ γc _ _ (fun m => raftSvc_encOf_InstallSnapshot (γs m) (snapPs m) a)
  meth_InstallSnapshot := rpcMeth_svcK P s _ _ _ _ _ γc _ n L.meth_InstallSnapshot
  enc_RequestPreVote := encOf_svcK _ γc _ _ (fun m => raftSvc_encOf_RequestPreVote (γs m) (snapPs m) a)
  meth_RequestPreVote := rpcMeth_svcK P s _ _ _ _ _ γc _ n L.meth_RequestPreVote
  enc_RequestVote := encOf_svcK _ γc _ _ (fun m => raftSvc_encOf_RequestVote (γs m) (snapPs m) a)
  meth_RequestVote := rpcMeth_svcK P s _ _ _ _ _ γc _ n L.meth_RequestVote
  enc_TimeoutNow := encOf_svcK _ γc _ _ (fun m => raftSvc_encOf_TimeoutNow (γs m) (snapPs m) a)
  meth_TimeoutNow := rpcMeth_svcK P s _ _ _ _ _ γc _ n L.meth_TimeoutNow

end rcv

end github_com.hashicorp.raft.examples.hraftnet

end Perennial

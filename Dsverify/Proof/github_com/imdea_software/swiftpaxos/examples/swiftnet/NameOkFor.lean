/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swiftnet/NameOkFor.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
The kit's `rpcName` meets `RpcNames` at each listed receiver (`*master.Master`, `*swift.Replica`):
`nameOkFor` (Proof/net/rpc/LocalRegister.lean), sorry-free, which the registrations use instead of
`kitNameOk` (false for an unlisted receiver: HUB-REQUEST 1 of the codec group).
-/
module

public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.examples.swiftnet.Codec
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.netrpc.rpc.LocalRegister

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

section codec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [examples.swiftnet.Assumptions]
variable [net.Assumptions] [net.FieldAssumptions] [net.rpc.Assumptions]

theorem kitNameOkFor (rcvr : GoInterface)
    (hm : ∃ p : Loc,
      rcvr = interface.mkOk (go.GoType.PointerType master.Master.ty) #p ∨
      rcvr = interface.mkOk (go.GoType.PointerType swift.Replica.ty) #p) :
    ⊢ net.rpc.nameOkFor (GF := GF) (net.rpc.kitFn go!"rpcName") rcvr := by
  have h := examples.swiftnet.nameOkC (GF := GF)
  unfold net.rpc.nameOkFor
  iintro !> %Φ HΦ
  rw [show net.rpc.RpcNames.name rcvr = examples.swiftnet.kitNameC rcvr from rfl]
  iapply h $$ %rcvr %Φ [] HΦ
  unfold examples.swiftnet.kitCodecC; dsimp only
  ipureintro; exact hm

theorem kitNameOkFor_master (p : Loc) :
    ⊢ net.rpc.nameOkFor (GF := GF) (net.rpc.kitFn go!"rpcName")
      (interface.mkOk (go.GoType.PointerType master.Master.ty) #p) :=
  kitNameOkFor _ ⟨p, Or.inl rfl⟩

theorem kitNameOkFor_replica (p : Loc) :
    ⊢ net.rpc.nameOkFor (GF := GF) (net.rpc.kitFn go!"rpcName")
      (interface.mkOk (go.GoType.PointerType swift.Replica.ty) #p) :=
  kitNameOkFor _ ⟨p, Or.inr rfl⟩

end codec

end Perennial.github_com.imdea_software.swiftpaxos

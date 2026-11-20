/-
Setting up a grpc address (`notes/grpc-model.md`), in a run's start-up update: allocate the world
(`grpcWorld_alloc`: the registry of connections, for given address-level method specs `MS`) and
fix an address's protocols as the grpc ones (`grpcAddr_set`, from the address's `addrUnset`,
once). After this, every party of address `a` uses `reqProto W a` / `respProto W a` and the
method specs `W.MS a`: no spec lets a proof choose another protocol or spec per side.
-/
module

public import Harness.Proof.grpc.Proto

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode NetConn

namespace google_golang_org.grpc

section setup
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netConnExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [G : GooseGlobalGS HasLC.hasLC GF]

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- A world for the method specs `MS`: a fresh, empty registry. -/
theorem grpcWorld_alloc (MS : GoString → GoString → Option (UnarySpec GF)) :
    ⊢@{IProp GF} |={⊤}=> ∃ W : GrpcWorld GF, ⌜W.MS = MS⌝ ∗ inv regN (regInv W) := by
  imod ghost_map_alloc_empty (K := w64) (V := GConnNames) (GF := GF) with ⟨%γ, H⟩
  imod inv_alloc regN ⊤ (regInv ⟨MS, γ⟩) $$ [H] with #Hinv
  · inext
    unfold regInv
    iexists ∅
    iframe H
    iapply BigSepM.bigSepM_empty.2
    iempintro
  imodintro
  iexists ⟨MS, γ⟩
  isplitr
  · ipureintro; rfl
  · iexact Hinv

/-- Address `a` serves the world `W`'s grpc protocol, for good. -/
theorem grpcAddr_set (W : GrpcWorld GF) (a : GoString) :
    ⊢@{IProp GF} addrUnset a -∗ inv regN (regInv W) ==∗ grpcAddr W a := by
  iintro Hu #Hinv
  imod addr_set_proto _ a (reqProto W a) (respProto W a) $$ Hu with #Hp
  imodintro
  unfold grpcAddr
  iframe Hp Hinv

end setup

end google_golang_org.grpc

end Perennial

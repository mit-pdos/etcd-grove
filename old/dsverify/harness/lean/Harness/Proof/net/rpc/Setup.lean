/-
Setting up an rpc address (`notes/craq-net.md`, "rpc specs"), in a run's start-up update: allocate
the world (`rpcWorld_alloc`: the registry of connections, for given address-level service specs
`SS`) and fix an address's protocols as the rpc ones (`rpcAddr_set`, from the address's
`addrUnset`, once). After this, every party of address `a` uses `reqProto W a` / `respProto W a`
and the services `W.SS a`: no spec lets a proof choose another protocol or service spec per side.
-/
module

public import Harness.Proof.net.rpc.Proto

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode NetConn

namespace net.rpc

section setup
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netConnExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [G : GooseGlobalGS HasLC.hasLC GF]

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- A world for the service specs `SS`: a fresh, empty registry. -/
theorem rpcWorld_alloc (SS : GoString → GoString → Option (MethodSpec GF)) :
    ⊢@{IProp GF} |={⊤}=> ∃ W : RpcWorld GF, ⌜W.SS = SS⌝ ∗ inv regN (regInv W) := by
  imod ghost_map_alloc_empty (K := w64) (V := RpcConnNames) (GF := GF) with ⟨%γ, H⟩
  imod inv_alloc regN ⊤ (regInv ⟨SS, γ⟩) $$ [H] with #Hinv
  · inext
    unfold regInv
    iexists ∅
    iframe H
    iapply BigSepM.bigSepM_empty.2
    iempintro
  imodintro
  iexists ⟨SS, γ⟩
  isplitr
  · ipureintro; rfl
  · iexact Hinv

/-- Address `a` serves the world `W`'s rpc protocol, for good. -/
theorem rpcAddr_set (W : RpcWorld GF) (a : GoString) :
    ⊢@{IProp GF} addrUnset a -∗ inv regN (regInv W) ==∗ rpcAddr W a := by
  iintro Hu #Hinv
  imod addr_set_proto _ a (reqProto W a) (respProto W a) $$ Hu with #Hp
  imodintro
  unfold rpcAddr
  iframe Hp Hinv

end setup

end net.rpc

end Perennial

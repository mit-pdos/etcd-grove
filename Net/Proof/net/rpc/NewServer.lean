/-
The proof of `NewServer` (`Net/Spec/net/rpc/NewServer.lean`): the services map made, the struct
allocated, its three mutexes given their invariants (the registry's ghost map allocated empty).
-/
module

public import Net.Spec.net.rpc.NewServer

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace net.rpc

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : net.rpc.Assumptions] [field_sem : net.FieldAssumptions]
variable [π : NetProtoGS] [sync.Assumptions]

theorem svcMap_alloc :
    ⊢ |={⊤}=> ∃ γ : GName, ghostMapAuth (GF := GF) γ 1 (∅ : GMap GoString Loc) := by
  iintro
  imod (ghost_map_alloc_empty (GF := GF) (K := GoString) (V := Loc)) with ⟨%γ, H⟩
  imodintro
  iexists γ
  iexact H

theorem NewServer.wp_proof : NewServer.spec (GF := GF) (hG := hG) := by
  wp_start
  iapply wp_fupd
  wp_auto
  wp_apply (wp_map_make1 (K := GoString) (V := Loc)) as %mp Hmp
  iStructNamed «$r0»
  imod svcMap_alloc (GF := GF) with ⟨%γ, Hγ⟩
  imod sync.init_Mutex (svcMapInvO γ none «$r0_ptr») ⊤
      (structFieldRef net.rpc.Server go!"mapLock" «$r0_ptr») $$ mapLock [serviceMap Hmp Hγ] with #Hmu
  · inext
    iunfold svcMapInvO
    iexists mp, ∅
    iframe serviceMap Hmp Hγ
    simp only [svcOwnIn]
    itrivial
  imod sync.init_Mutex (reqFreeInv «$r0_ptr») ⊤
      (structFieldRef net.rpc.Server go!"reqLock" «$r0_ptr») $$ reqLock [freeReq] with #Hrq
  · inext
    iunfold reqFreeInv
    iexists null, []
    iframe freeReq
    iunfold reqChain
    ipureintro; rfl
  imod sync.init_Mutex (respFreeInv «$r0_ptr») ⊤
      (structFieldRef net.rpc.Server go!"respLock" «$r0_ptr») $$ respLock [freeResp] with #Hrs
  · inext
    iunfold respFreeInv
    iexists null, []
    iframe freeResp
    iunfold respChain
    ipureintro; rfl
  imodintro
  iapply HΦ
  iexists γ
  iunfold isServer
  iunfold isServerO
  iframe Hpkg Hmu Hrq Hrs

end proof

end net.rpc
end Perennial

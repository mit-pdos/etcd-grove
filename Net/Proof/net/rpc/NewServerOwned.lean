/-
The proof of `NewServer.spec_owned` (`Net/Spec/net/rpc/NewServer.lean`): `NewServer`'s proof
(`NewServer.lean`), with the owner's ghost map allocated empty too: `mapLock`'s invariant holds its
elements (none: the services map is empty), the owner keeps its authority (`svcOwn γf ∅`).
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

private theorem svcMap_alloc_owned :
    ⊢ |={⊤}=> ∃ γ γf : GName, ghostMapAuth (GF := GF) γ 1 (∅ : GMap GoString Loc) ∗
      ghostMapAuth (GF := GF) γf 1 (∅ : GMap GoString Unit) := by
  iintro
  imod (ghost_map_alloc_empty (GF := GF) (K := GoString) (V := Loc)) with ⟨%γ, H⟩
  imod (ghost_map_alloc_empty (GF := GF) (K := GoString) (V := Unit)) with ⟨%γf, Hf⟩
  imodintro
  iexists γ, γf
  iframe H Hf

theorem NewServer.wp_proof_owned : NewServer.spec_owned (GF := GF) (hG := hG) := by
  wp_start
  iapply wp_fupd
  wp_auto
  wp_apply (wp_map_make1 (K := GoString) (V := Loc)) as %mp Hmp
  iStructNamed «$r0»
  imod svcMap_alloc_owned (GF := GF) with ⟨%γ, %γf, Hγ, Hγf⟩
  imod sync.init_Mutex (svcMapInvO γ (some γf) «$r0_ptr») ⊤
      (structFieldRef net.rpc.Server go!"mapLock" «$r0_ptr») $$ mapLock [serviceMap Hmp Hγ] with #Hmu
  · inext
    iunfold svcMapInvO
    iexists mp, ∅
    iframe serviceMap Hmp Hγ
    simp only [svcOwnIn]
    iapply BigSepM.bigSepM_empty.2
    iempintro
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
  iexists γ, γf
  iunfold svcOwn
  iframe Hγf
  iunfold isServerO
  iframe Hpkg Hmu Hrq Hrs

end proof

end net.rpc
end Perennial

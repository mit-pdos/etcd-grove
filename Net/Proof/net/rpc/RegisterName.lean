/-
The proof of `RegisterName` (`Net/Spec/net/rpc/RegisterName.lean`): `DefaultServer` loaded, then
`Server.RegisterName`.
-/
module

public import Net.Spec.net.rpc.RegisterName

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace net.rpc

section sec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : net.rpc.Assumptions]
variable [π : NetProtoGS]

theorem RegisterName.wp_proof
    (wp_RegisterName : Server.RegisterName.spec (GF := GF) (hG := hG)) :
    RegisterName.spec (GF := GF) (hG := hG) := by
  intro γ C name rcvr S nm np hname
  wp_start as ⟨#Hd, #Hset, Hrcv⟩
  iunfold defaultServer at Hd
  icases Hd with ⟨%s, #Hg, #Hs⟩
  wp_auto
  wp_apply wp_RegisterName s γ C name rcvr S nm np hname $$ [$Hs $Hset $Hrcv] as %err Hr
  iapply HΦ
  iexact Hr

end sec

end net.rpc
end Perennial

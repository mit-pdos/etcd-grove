/-
The proof of `Register.spec_none` (`Net/Spec/net/rpc/Register.lean`): `DefaultServer` loaded,
then `Server.Register.spec_none`.
-/
module

public import Net.Spec.net.rpc.Register

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
variable [package_sem' : net.rpc.Assumptions] [field_sem : net.FieldAssumptions]
variable [π : NetProtoGS]

theorem Register.wp_proof_none
    (wp_Register : Server.Register.spec_none (GF := GF) (hG := hG)) :
    Register.spec_none (GF := GF) (hG := hG) := by
  intro γ C rcvr nm c rest hnm hc
  wp_start as ⟨#Hd, #Hset, Hrcv, #Hlog⟩
  iunfold defaultServerAny at Hd
  icases Hd with ⟨%s, #Hg, #Hs⟩
  wp_auto
  wp_apply wp_Register s γ C rcvr nm c rest hnm hc $$ [$Hs $Hset $Hrcv $Hlog] as %err Hr
  iapply HΦ
  iexact Hr


end sec

end net.rpc
end Perennial

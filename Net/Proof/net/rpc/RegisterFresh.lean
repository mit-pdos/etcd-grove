/-
The proof of `Register.spec_fresh` (`Net/Spec/net/rpc/Register.lean`): `DefaultServer` loaded,
then `Server.Register.spec_fresh`.
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

theorem Register.wp_proof_fresh
    (wp_Register : Server.Register.spec_fresh (GF := GF) (hG := hG)) :
    Register.spec_fresh (GF := GF) (hG := hG) := by
  intro γ γf R C rcvr S nm c rest hnm hc
  wp_start as ⟨#Hd, HR, %HnR, #Hset, Hrcv⟩
  iunfold defaultServerO at Hd
  icases Hd with ⟨%s, #Hg, #Hs⟩
  wp_auto
  wp_apply wp_Register s γ γf R C rcvr S nm c rest hnm hc $$ [$Hs $HR $Hset $Hrcv] as %err Hr
  · ipureintro; exact HnR
  iapply HΦ
  iexact Hr

end sec

end net.rpc
end Perennial

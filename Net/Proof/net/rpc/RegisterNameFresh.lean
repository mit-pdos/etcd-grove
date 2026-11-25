/-
The proof of `RegisterName.spec_fresh` (`Net/Spec/net/rpc/RegisterName.lean`): `DefaultServer`
loaded, then `Server.RegisterName.spec_fresh`.
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
variable [package_sem' : net.rpc.Assumptions] [field_sem : net.FieldAssumptions]
variable [π : NetProtoGS]

theorem RegisterName.wp_proof_fresh
    (wp_RegisterName : Server.RegisterName.spec_fresh (GF := GF) (hG := hG)) :
    RegisterName.spec_fresh (GF := GF) (hG := hG) := by
  intro γ γf R C name rcvr S nm np hname
  wp_start as ⟨#Hd, HR, %HnR, #Hset, Hrcv⟩
  iunfold defaultServerO at Hd
  icases Hd with ⟨%s, #Hg, #Hs⟩
  wp_auto
  wp_apply wp_RegisterName s γ γf R C name rcvr S nm np hname $$ [$Hs $HR $Hset $Hrcv] as %err Hr
  · ipureintro; exact HnR
  iapply HΦ
  iexact Hr

end sec

end net.rpc
end Perennial

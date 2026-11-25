/-
The proof of `Server.RegisterName.spec_fresh` (`Net/Spec/net/rpc/Server__RegisterName.lean`):
`register`'s fresh spec, with `useName`.
-/
module

public import Net.Spec.net.rpc.Server__RegisterName

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

theorem Server.RegisterName.wp_proof_fresh
    (wp_register : Server.register.spec_fresh (GF := GF) (hG := hG)) :
    Server.RegisterName.spec_fresh (GF := GF) (hG := hG) := by
  intro s γ γf R C name rcvr S nm np hname
  wp_start as ⟨#Hs, HR, %HnR, #Hset, Hrcv⟩
  wp_auto
  wp_apply wp_register s γ γf R C rcvr S nm np name true
      (by simp only [regNameOk, ite_true]; exact hname)
      $$ [$Hs $HR $Hset $Hrcv] as %err Hr
  · ipureintro; simpa using HnR
  iapply HΦ
  try simp only [ite_true]
  iexact Hr

end sec

end net.rpc
end Perennial

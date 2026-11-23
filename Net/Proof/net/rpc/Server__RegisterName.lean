/-
The proof of `Server.RegisterName` (`Net/Spec/net/rpc/Server__RegisterName.lean`): `register`.
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

theorem Server.RegisterName.wp_proof (wp_register : Server.register.spec (GF := GF) (hG := hG)) :
    Server.RegisterName.spec (GF := GF) (hG := hG) := by
  intro s γ C name rcvr S nm np hname
  wp_start as ⟨#Hs, #Hset, Hrcv⟩
  wp_auto
  wp_apply wp_register s γ C rcvr S nm np name true
      (by simp only [regNameOk, ite_true]; exact hname)
      $$ [$Hs $Hset $Hrcv] as %err Hr
  iapply HΦ
  iexact Hr

end sec

end net.rpc
end Perennial

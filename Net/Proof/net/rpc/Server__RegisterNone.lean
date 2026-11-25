/-
The proof of `Server.Register.spec_none` (`Net/Spec/net/rpc/Server__Register.lean`): `register`'s
`spec_none`, without `useName`.
-/
module

public import Net.Spec.net.rpc.Server__Register

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
variable [π : NetProtoGS] [log.Assumptions]

theorem Server.Register.wp_proof_none
    (wp_register : Server.register.spec_none (GF := GF) (hG := hG)) :
    Server.Register.spec_none (GF := GF) (hG := hG) := by
  intro s γ C rcvr nm c rest hnm hc
  wp_start as ⟨#Hs, #Hset, Hrcv, #Hlog⟩
  wp_auto
  wp_apply wp_register s γ C rcvr nm [] false
      (by simp only [regNameOk, Bool.false_eq_true, ite_false]; exact ⟨trivial, c, rest, hnm, hc⟩)
      $$ [$Hs $Hset $Hrcv $Hlog] as %err Hr
  iapply HΦ
  iexact Hr


end sec

end net.rpc
end Perennial

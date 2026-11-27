/-
The proof of `Server.Register.spec_fresh` (`Net/Spec/net/rpc/Server__Register.lean`): `register`'s
fresh spec, without `useName`.
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
variable [package_sem' : net.rpc.Assumptions]
variable [π : NetProtoGS]

theorem Server.Register.wp_proof_fresh
    (wp_register : Server.register.spec_fresh (GF := GF) (hG := hG)) :
    Server.Register.spec_fresh (GF := GF) (hG := hG) := by
  intro s γ γf R C rcvr S nm c rest hnm hc
  wp_start as ⟨#Hs, HR, %HnR, #Hset, Hrcv⟩
  wp_auto
  wp_apply wp_register s γ γf R C rcvr S nm false [] false
      (by simp only [regNameOk, Bool.false_eq_true, ite_false]; exact ⟨trivial, c, rest, hnm, hc⟩)
      $$ [$Hs $HR $Hset $Hrcv] as %err Hr
  · ipureintro; simpa using HnR
  iapply HΦ
  try simp only [Bool.false_eq_true, ite_false]
  iexact Hr

end sec

end net.rpc
end Perennial

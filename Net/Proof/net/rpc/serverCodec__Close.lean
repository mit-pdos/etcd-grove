/-
The proof of `serverCodec.Close` (`Net/Spec/net/rpc/serverCodec__Close.lean`): the `closed` flag,
then `rwc`'s `Close`.
-/
module

public import Net.Spec.net.rpc.serverCodec__Close

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace net.rpc

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : net.rpc.Assumptions]

theorem serverCodec.Close.wp_proof (wp_Close : net.Conn.Close.spec (GF := GF) (hG := hG)) :
    serverCodec.Close.spec (GF := GF) (hG := hG) := by
  intro c t cn s a la ra b Q
  wp_start as ⟨#Hrwc, #Hc, Hcl, Hau⟩
  wp_auto
  cases b with
  | true =>
    wp_auto
    iapply HΦ
    iframe Hcl
    simp only [↓reduceIte]
    ipureintro; trivial
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    wp_auto
    wp_apply wp_Close t cn s a la ra Q $$ [$Hc $Hau] as %err Hres
    iapply HΦ
    iframe Hcl
    iexact Hres
end proof

end net.rpc
end Perennial

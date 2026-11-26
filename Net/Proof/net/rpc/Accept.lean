/-
`rpc.Accept`'s proof: load `DefaultServer`, call its `Accept` (`Server.Accept.spec`). Lean-first.
-/
module

public import Net.Spec.net.rpc.Accept
public import Net.Spec.net.rpc.Server__Accept

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

theorem Accept.wp_proof (wp_Accept : Server.Accept.spec (GF := GF) (hG := hG)) :
    Accept.spec (GF := GF) (hG := hG) := by
  intro γs C W la lis l
  wp_start as ⟨%hT, #Hd, #Haddr, #Henv, #Hset, #Hlog, #Hlis, Hon, Hinv⟩
  iunfold defaultServerAny at Hd
  icases Hd with ⟨%s, #Hg, #Hs⟩
  wp_auto
  wp_apply wp_Accept s γs C W la lis l $$ [$Hs $Haddr $Henv $Hset $Hlog $Hlis $Hon $Hinv]
  · ipureintro; exact hT
  iapply HΦ
  itrivial

end sec

end net.rpc
end Perennial

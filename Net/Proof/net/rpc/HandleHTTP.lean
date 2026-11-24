/-
`rpc.HandleHTTP`'s proof: load `DefaultServer`, call its `HandleHTTP` at `DefaultRPCPath` and
`DefaultDebugPath` (`Server.HandleHTTP.spec`). Lean-first.
-/
module

public import Net.Spec.net.rpc.HandleHTTP

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

theorem litPattern_rpc : net.http.litPattern defaultRPCPath := by
  unfold net.http.litPattern defaultRPCPath; decide

theorem litPattern_debug : net.http.litPattern defaultDebugPath := by
  unfold net.http.litPattern defaultDebugPath; decide

theorem HandleHTTP.wp_proof (wp_HandleHTTP : Server.HandleHTTP.spec (GF := GF) (hG := hG)) :
    HandleHTTP.spec (GF := GF) (hG := hG) := by
  intro γs C W A Ps hrp hdp
  wp_start as ⟨%hT, #Hhttp, Hmux, #Hd, #Hsrv, #Henv, #Hset, #Hcon⟩
  iunfold defaultServerAny at Hd
  icases Hd with ⟨%s, #Hg, #Hs⟩
  wp_auto
  wp_apply wp_HandleHTTP s γs C W A Ps defaultRPCPath defaultDebugPath litPattern_rpc
      litPattern_debug (by decide) hrp hdp $$ [Hmux] as ⟨Hmux, #Hr⟩
  · iframe Hhttp Hmux Hs Hsrv Henv Hset Hcon
    ipureintro; exact hT
  iapply HΦ
  iframe Hmux Hr

end sec

end net.rpc
end Perennial

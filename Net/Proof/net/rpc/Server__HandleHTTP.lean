/-
`(*Server).HandleHTTP`'s proof: two `http.Handle`s (`Handle.spec`), the first's route an rpc handler
at every address with `A`: the server's `ServeHTTP` (`Server.ServeHTTP.spec`). Lean-first.
-/
module

public import Net.Spec.net.rpc.Server__HandleHTTP
public import Net.Spec.net.rpc.Server__ServeHTTP
public import Net.Spec.net.http.Handle

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

theorem Server.HandleHTTP.wp_proof (wp_Handle : net.http.Handle.spec (GF := GF) (hG := hG))
    (wp_ServeHTTP : Server.ServeHTTP.spec (GF := GF) (hG := hG)) :
    Server.HandleHTTP.spec (GF := GF) (hG := hG) := by
  intro s γs C W A Ps rp dp hrp hdp hne hrpP hdpP
  wp_start as ⟨%hT, #Hhttp, Hmux, #Hs, #Hsrv, #Henv, #Hset, #Hcon⟩
  wp_auto
  wp_apply wp_Handle Ps rp _ hrp hrpP (by simp [interface.mkOk]) $$ [$Hhttp $Hmux]
    as ⟨Hmux, #Hroute⟩
  wp_auto
  wp_apply wp_Handle (rp :: Ps) dp _ hdp (by simp [hdpP, Ne.symm hne])
    (by simp [interface.mkOk]) $$ [$Hhttp $Hmux] as ⟨Hmux, -⟩
  wp_auto
  iapply HΦ
  iframe Hmux
  iunfold net.http.muxRpc
  iexists _
  iframe Hroute
  imodintro
  iintro %a %hA
  icases Hsrv $$ %a %hA with ⟨#Hss, %hhs⟩
  iunfold net.http.rpcHjHandler
  isplitr
  · ipureintro; exact hhs
  iexists _
  isplitr
  · ipureintro; rfl
  imodintro
  iintro %cn %rp' %req %D %Φ' ⟨#Hhead, Hhj, Htt⟩ HΦ'
  iapply (wp_ServeHTTP s γs C W a cn rp' req D) $$ [Hhj Htt] HΦ'
  iframe Hs Hss Henv Hset Hcon Hhead Hhj Htt
  ipureintro
  exact ⟨hT, hhs⟩

end sec

end net.rpc
end Perennial

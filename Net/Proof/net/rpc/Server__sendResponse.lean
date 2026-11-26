/-
The proof of `Server.sendResponse` (`Net/Spec/net/rpc/Server__sendResponse.lean`): a free
`*Response` (`getResponse`), its fields set (`invalidRequest` as the reply of an error response),
then under `sending` (`srvSendInv`) the codec's `WriteResponse`: with no write error yet, the
update `respUpd` answers the request (`answer`) and extends the record of answers (`resp_step`);
the write's result, whole or in part (its error then sticky), keeps `srvSendInv`. `debugLog` is
`false`; the response goes back to its free list.
-/
module

public import Net.Spec.net.rpc.Server__sendResponse
public import Net.Spec.net.rpc.Server__getResponse
public import Net.Spec.net.rpc.Server__freeResponse
public import Net.Spec.net.rpc.serverCodec__WriteResponse
public import Net.Proof.net.rpc.ServerGhost
public import Perennial.Spec.sync.Mutex__Lock
public import Perennial.Spec.sync.Mutex__Unlock

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option maxHeartbeats 800000

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace net.rpc

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : net.rpc.Assumptions]
variable [π : NetProtoGS] [sync.Assumptions] [net.Assumptions]

attribute [local instance] GooseGlobalGS.gooseInvGS

theorem Server.sendResponse.wp_proof (wp_Lock : sync.Mutex.Lock.spec (GF := GF) (hG := hG))
    (wp_Unlock : sync.Mutex.Unlock.spec (GF := GF) (hG := hG))
    (wp_getResponse : Server.getResponse.spec (GF := GF) (hG := hG))
    (wp_freeResponse : Server.freeResponse.spec (GF := GF) (hG := hG))
    (wp_WriteResponse : serverCodec.WriteResponse.spec (GF := GF) (hG := hG)) :
    Server.sendResponse.spec (GF := GF) (hG := hG) := by
  intro s γs C W a sc t cn la ra sending req rqv reply errmsg k Φc
  wp_start as ⟨#Hsrv, #Henv, #Hset, #Hsc, #Hmu, Hreq, %Hseq, Hpend, Hres⟩
  iunfold srvEnv at Henv
  icases Henv with ⟨#Hcli, #Hir⟩
  ihave #Hcli' := Hcli
  iunfold cliEnv at Hcli'
  icases Hcli' with ⟨%eof, %ueof, %ed, #Hio, #Hsync, #Heof, #Hueof, #Hed, #HefV, #HesV, #Hdbg⟩
  iunfold srvCodecAt at Hsc
  icases Hsc with ⟨#Hrwc, #Hconn⟩
  wp_auto
  wp_apply wp_getResponse s γs $$ Hsrv as %resp Hresp
  by_cases he : errmsg = []
  rw [decide_eq_true he]
  simp only [Bool.not_true, ↓reduceIte, Bool.false_eq_true]
  wp_auto
  ihave Hpk : (∃ body : GoInterface, reply_ptr ↦ body ∗
      resp ↦ (net.rpc.Response.mk rqv.ServiceMethod' rqv.Seq' errmsg null) ∗
      respEnc C errmsg body (fun eb => Φc eb errmsg) : IProp GF) $$ [reply Hresp Hres]
  · iexists reply
    subst he
    iframe reply Hresp
    iunfold respEnc
    iunfold ansRes at Hres
    simp only [↓reduceIte]
    iexact Hres
  rotate_left
  rw [decide_eq_false he]
  simp only [Bool.not_false, ↓reduceIte]
  wp_auto
  ihave Hpk : (∃ body : GoInterface, reply_ptr ↦ body ∗
      resp ↦ (net.rpc.Response.mk rqv.ServiceMethod' rqv.Seq' errmsg null) ∗
      respEnc C errmsg body (fun eb => Φc eb errmsg) : IProp GF) $$ [reply Hresp Hres]
  · iexists _
    iframe reply Hresp
    iunfold respEnc
    iunfold ansRes at Hres
    simp only [he, ↓reduceIte]
    iexact Hres
  rotate_left
  all_goals (
    icases Hpk with ⟨%body, reply, Hresp, Hbody⟩
    wp_apply +noauto wp_Lock _ _ $$ [$Hsync $Hmu] as ⟨Hlk, Hinv⟩
    iunfold srvSendInv at Hinv
    icases Hinv with ⟨%w0, %Wd, %Rs, Hwerr, Hsend, Hrec, #Hsl, ⟨%HRs, %HWd, %Hw0⟩⟩
    wp_auto_lc 1
    cases w0 with
    | ok e =>
      wp_apply wp_WriteResponse sc t cn true a la ra resp _ body (interface.ok e) ed C
          (respProto (Gg := hG.goose_globalGS) W a) Wd (fun eb => Φc eb errmsg) (fun _ => iprop(True))
          $$ [$Hrwc $Hconn $Hed $Hwerr $Hresp $Hset $Hsend $Hbody] as %err ⟨Hresp, Hout⟩
      · iintro %h; cases h
      icases Hout with (⟨%He, Hwerr, Hsend, -⟩ | ⟨%Hc, -⟩)
      · subst He
        wp_apply wp_Unlock _ (srvSendInv W a cn sc) $$ [$Hsync $Hmu $Hlk Hwerr Hsend Hrec]
        · iunfold srvSendInv
          iexists _, Wd, Rs
          iframe Hwerr Hsend Hrec Hsl
          ipureintro; exact ⟨HRs, HWd, Hw0⟩
        wp_apply wp_freeResponse s γs resp _ $$ [$Hsrv $Hresp]
        iapply HΦ; iexact Hreq
      · exact Hc.elim
    | nil =>
      ihave ⟨Hpend, #HhsA⟩ := ansPend_hsAns W a cn k _ Φc $$ Hpend
      ihave %Hpre := sendTok_sentLb_prefix (Gg := hG.goose_globalGS) cn true _ Wd (W.hsAns a)
        $$ Hsend HhsA
      have hWd : Wd = W.hsAns a ++ respsWire Rs := by
        rcases Hw0 rfl with h | ⟨hR, hp⟩
        · exact h
        · have h0 : respsWire ([] : List Ans) = [] := by simp [respsWire, framesOf_nil]
          rw [hR, h0, List.append_nil]
          exact hp.eq_of_length (Nat.le_antisymm hp.length_le Hpre.length_le)
      have hwf : ∀ eb, Wd ++ respWire rqv.Seq' rqv.ServiceMethod' errmsg eb =
          W.hsAns a ++ respsWire (Rs ++ [(k, rqv.ServiceMethod', errmsg, eb)]) := fun eb => by
        rw [respsWire_snoc, hWd, Hseq, List.append_assoc]
      ihave Hupd : (⌜(interface.nil : GoInterface) = interface.nil⌝ -∗ respUpd (hG := hG) cn
          (respProto (Gg := hG.goose_globalGS) W a) Wd rqv.Seq' rqv.ServiceMethod' errmsg
          (fun eb => Φc eb errmsg)
          (fun eb => iprop(ansRec W a cn (Rs ++ [(k, rqv.ServiceMethod', errmsg, eb)]) ∗
            ⌜ansOk (k, rqv.ServiceMethod', errmsg, eb)⌝))) $$ [Hpend Hrec Hlc1]
      · iintro -
        iunfold respUpd
        iintro %eb %hfit HΦc
        imod answer W a cn k rqv.ServiceMethod' Φc errmsg eb $$ [$Hlc1 $Hpend $HΦc]
          with ⟨%γ, #Hrpc, #Hel, %hk⟩
        have hx : ansOk (k, rqv.ServiceMethod', errmsg, eb) := ⟨hfit.1, hfit.2, hk⟩
        icases resp_step W a cn γ Rs (k, rqv.ServiceMethod', errmsg, eb) (fun y hy => by
            rcases List.mem_append.1 hy with h | h
            · exact HRs y h
            · simp at h; subst h; exact hx) $$ [$Hrpc $Hsl $Hel $Hrec] with ⟨#HP, Hrec⟩
        imodintro
        rw [hwf eb]
        dsimp only
        iframe HP Hrec
        ipureintro; exact hx
      wp_apply wp_WriteResponse sc t cn true a la ra resp _ body interface.nil ed C
          (respProto (Gg := hG.goose_globalGS) W a) Wd (fun eb => Φc eb errmsg)
          (fun eb => iprop(ansRec W a cn (Rs ++ [(k, rqv.ServiceMethod', errmsg, eb)]) ∗
            ⌜ansOk (k, rqv.ServiceMethod', errmsg, eb)⌝))
          $$ [$Hrwc $Hconn $Hed $Hwerr $Hresp $Hset $Hsend $Hbody $Hupd] as %err ⟨Hresp, Hout⟩
      icases Hout with (⟨%Hne, -⟩ | ⟨-, %eb, ⟨Hrec, %Hx⟩, Hout⟩)
      · exact Hne.elim
      have hRs' : ∀ y ∈ Rs ++ [(k, rqv.ServiceMethod', errmsg, eb)], ansOk y := fun y hy => by
        rcases List.mem_append.1 hy with h | h
        · exact HRs y h
        · simp at h; subst h; exact Hx
      have hw := (hwf eb).symm
      icases Hout with (⟨%He, Hwerr, Hsend⟩ | ⟨%w, %kk, ⟨%Hw, %Hwne⟩, Hwerr, Hsend, #HE⟩)
      · subst He
        wp_apply wp_Unlock _ (srvSendInv W a cn sc) $$ [$Hsync $Hmu $Hlk Hwerr Hsend Hrec]
        · iunfold srvSendInv
          iexists _, _, _
          iframe Hwerr Hsend Hrec Hsl
          ipureintro
          exact ⟨hRs', by rw [hw]; exact List.prefix_refl _, fun _ => Or.inl hw.symm⟩
        wp_apply wp_freeResponse s γs resp _ $$ [$Hsrv $Hresp]
        iapply HΦ; iexact Hreq
      · ihave %Hnet := net.resErr_netErr _ _ _ _ _ _ _ $$ HE
        obtain ⟨-, Hne⟩ := Hnet
        obtain ⟨pe, rfl⟩ := Hne (by simp)
        wp_apply wp_Unlock _ (srvSendInv W a cn sc) $$ [$Hsync $Hmu $Hlk Hwerr Hsend Hrec]
        · iunfold srvSendInv
          iexists _, _, _
          iframe Hwerr Hsend Hrec Hsl
          ipureintro
          refine ⟨hRs', by rw [hw]; exact (List.prefix_append_right_inj _).2 Hw, fun h => ?_⟩
          exact absurd h (by simp [interface.mkOk])
        wp_apply wp_freeResponse s γs resp _ $$ [$Hsrv $Hresp]
        iapply HΦ; iexact Hreq)

end proof

end net.rpc
end Perennial

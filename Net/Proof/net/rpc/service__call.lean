/-
The proof of `service.call` (`Net/Spec/net/rpc/service__call.lean`): `wg.Done()` deferred (the
join's `ownDone`, `sync.tokJoin.WaitGroup.wp_Done`, which gives the slot's thread token back), the
counter incremented under the method's mutex, the method's call (`callReady`'s `WP`), the error's
message (`errMsg`'s `Error()`, or `errAny`'s: any message, the answer given for each) or `""`, the response (`sendResponse`, whose `ansRes` is `callRet`'s
outcome), `req` freed.
-/
module

public import Net.Spec.net.rpc.service__call
public import Net.Spec.net.rpc.Server__sendResponse
public import Net.Spec.net.rpc.Server__freeRequest
public import Perennial.Spec.sync.Mutex__Lock
public import Perennial.Spec.sync.Mutex__Unlock
public import Perennial.Proof.sync.Results

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace net.rpc

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : net.rpc.Assumptions] [field_sem : net.FieldAssumptions]
variable [π : NetProtoGS] [sync.Assumptions]

attribute [local instance] GooseGlobalGS.gooseInvGS

theorem service.call.wp_proof (wp_Lock : sync.Mutex.Lock.spec (GF := GF) (hG := hG))
    (wp_Unlock : sync.Mutex.Unlock.spec (GF := GF) (hG := hG))
    (wp_sendResponse : Server.sendResponse.spec (GF := GF) (hG := hG))
    (wp_freeRequest : Server.freeRequest.spec (GF := GF) (hG := hG)) :
    service.call.spec (GF := GF) (hG := hG) := by
  intro svc s γs C W a sc t cn la ra sending wg mt req rqv argv replyv k Φc
  wp_start as ⟨#Hsrv, #Henv, #Hset, #Hsc, #Hmu, Hreq, ⟨%Hseq, %Hwg⟩, Hpend, Hcall, Hdone⟩
  ihave #Hsync := isServerAny_sync s γs $$ Hsrv
  iunfold callReady at Hcall
  icases Hcall with ⟨%rcvr, %mm, %v, #Hrcvr, #Hm, #Hv, #Hmmu, Hwp⟩
  wp_apply wp_with_defer as %defer Hdefer
  rw [decide_eq_false Hwg]
  wp_auto
  rw [MethodUnfold.method_unfold (t := go.GoType.PointerType net.rpc.methodType.ty) (m := go!"Lock")]
  wp_auto
  wp_apply wp_Lock _ _ $$ [$Hsync $Hmmu] as ⟨Hlk, ⟨%n, Hn⟩⟩
  rw [MethodUnfold.method_unfold (t := go.GoType.PointerType net.rpc.methodType.ty) (m := go!"Unlock")]
  wp_auto
  wp_apply wp_Unlock _ iprop(∃ n : w64, structFieldRef net.rpc.methodType go!"numCalls" mt ↦ n)
      $$ [$Hsync $Hmmu $Hlk Hn]
  · iexists _; iexact Hn
  ihave #Hv2 := Hv
  iStructNamed Hv2
  wp_auto
  wp_bind (App (App (App (Val #v.Call') (Val #rcvr)) (Val #argv)) (Val #replyv))
  iapply wp_wand $$ Hwp
  iintro %r' ⟨%e, %Hr', Hret⟩
  subst Hr'
  wp_auto
  iunfold callRet at Hret
  icases Hret with (⟨%He, Henc⟩ | ⟨%msg, #Hmsg, Hm⟩ | ⟨#Hany, Hm⟩)
  · subst He
    wp_auto
    wp_apply wp_sendResponse s γs C W a sc t cn la ra sending req rqv replyv [] k Φc
        $$ [$Hsrv $Henv $Hset $Hsc $Hmu $Hreq $Hpend Henc] as Hreq
    · isplitr
      · ipureintro; exact Hseq
      iunfold ansRes
      simp only [↓reduceIte]
      iexact Henc
    wp_apply wp_freeRequest s γs req rqv $$ [$Hsrv $Hreq]
    wp_apply sync.tokJoin.WaitGroup.wp_Done srvWgN iprop(False) wg iprop(True) $$ [$Hsync $Hdone]
      as Htok
    iapply HΦ; iexact Htok
  · ihave #Hmsg' := Hmsg
    iunfold errMsg at Hmsg'
    icases Hmsg' with ⟨%ei, %Hei, %Hty, #HW⟩
    subst Hei
    wp_auto
    wp_bind (App (Val #(methods ei.ty go!"Error" ei.v)) (Val #()))
    iapply HW
    inext
    wp_auto
    wp_apply wp_sendResponse s γs C W a sc t cn la ra sending req rqv replyv msg k Φc
        $$ [$Hsrv $Henv $Hset $Hsc $Hmu $Hreq $Hpend Hm] as Hreq
    · isplitr
      · ipureintro; exact Hseq
      iunfold ansRes
      iexact Hm
    wp_apply wp_freeRequest s γs req rqv $$ [$Hsrv $Hreq]
    wp_apply sync.tokJoin.WaitGroup.wp_Done srvWgN iprop(False) wg iprop(True) $$ [$Hsync $Hdone]
      as Htok
    iapply HΦ; iexact Htok
  · ihave #Hany' := Hany
    iunfold models_lab.errAny at Hany'
    icases Hany' with ⟨%ei, %Hei, %Hty, #HW⟩
    subst Hei
    wp_auto
    wp_bind (App (Val #(methods ei.ty go!"Error" ei.v)) (Val #()))
    iapply HW
    inext
    iintro %msg
    ihave Hm := Hm $$ %msg
    wp_auto
    wp_apply wp_sendResponse s γs C W a sc t cn la ra sending req rqv replyv msg k Φc
        $$ [$Hsrv $Henv $Hset $Hsc $Hmu $Hreq $Hpend Hm] as Hreq
    · isplitr
      · ipureintro; exact Hseq
      iunfold ansRes
      iexact Hm
    wp_apply wp_freeRequest s γs req rqv $$ [$Hsrv $Hreq]
    wp_apply sync.tokJoin.WaitGroup.wp_Done srvWgN iprop(False) wg iprop(True) $$ [$Hsync $Hdone]
      as Htok
    iapply HΦ; iexact Htok

end proof

end net.rpc
end Perennial

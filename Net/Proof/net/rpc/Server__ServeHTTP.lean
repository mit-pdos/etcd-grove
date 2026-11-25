/-
The proof of `Server.ServeHTTP` (`Net/Spec/net/rpc/Server__ServeHTTP.lean`): the request is a
`CONNECT` (`reqHead`); `Hijack` through the response (`hijackOk`): the acceptor's end with the head
read and nothing written; the head read gives the connection's names (`req_of_read`) and that the
dialer wrote its handshake (`recvTok_keep_sentLb`), so the answer meets `respProto` (`hsAns_proto`);
it is written by `Conn.Write` (`writeP`, `write_acc`), whole or a prefix (the error is not looked
at), which with the end's read deadline cleared by the hijack (or its reading dead) is
`rpcAccepted`; then `ServeConn`.
-/
module

public import Net.Spec.net.rpc.Server__ServeHTTP
public import Net.Spec.net.rpc.Server__ServeConn
public import Net.Spec.net.Conn__Write
public import Net.Proof.net.rpc.ServerGhost

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
variable [package_sem' : net.rpc.Assumptions]
variable [π : NetProtoGS] [net.Assumptions] [net.http.Assumptions]

/-- A prefix of the acceptor's handshake answer meets `respProto`, once the dialer's handshake was
written, before any answer. -/
theorem hsAns_proto (W : RpcWorld GF) (a : GoString) (cn : Nat) (γ : RpcConnNames) (bs : List w8)
    (h : bs <+: W.hsAns a) :
    isRpcConn (Gg := hG.goose_globalGS) W a cn γ ∗ sentLb (Gg := hG.goose_globalGS) cn false (W.hs a) ⊢
      □ respProto (Gg := hG.goose_globalGS) W a cn bs := by
  iintro ⟨#Hrpc, #Hsl⟩
  imodintro
  iunfold respProto
  ileft
  iexists γ, []
  iframe Hrpc Hsl
  isplitr
  · iapply BigSepL.bigSepL_nil.2; iempintro
  ipureintro
  refine ⟨by simp, ?_⟩
  simpa [respsWire, framesOf_nil] using h

theorem response_ptr_isHijacker :
    go.typeSetContains (go.GoType.PointerType net.http.response.ty) net.http.Hijacker.ty = true := by
  go_type_set

theorem Server.ServeHTTP.wp_proof (wp_Write : net.Conn.Write.spec (GF := GF) (hG := hG))
    (wp_ServeConn : Server.ServeConn.spec (GF := GF) (hG := hG)) :
    Server.ServeHTTP.spec (GF := GF) (hG := hG) := by
  intro s γs C W a cn rp req D
  wp_start as ⟨%Hb, #Hsrv, #Hserves, #Henv, #Hset, #Hcon, ⟨%Hhs, %HhsA⟩, #Hreq, Hhj, Htok⟩
  iunfold net.http.reqHead at Hreq
  icases Hreq with ⟨#Hm, %ra, #Hra⟩
  ihave #Henv' := Henv
  iunfold srvEnv at Henv'
  icases Henv' with ⟨#Hcli, -⟩
  iunfold cliEnv at Hcli
  icases Hcli with ⟨%eof, %ueof, %ed, -, -, -, -, #Hed, -, -, -⟩
  wp_auto
  simp only [response_ptr_isHijacker, ↓reduceIte]
  wp_auto
  wp_bind (App (Val #(methods (go.GoType.PointerType net.http.response.ty) go!"Hijack" #rp))
    (Val #()))
  iunfold net.http.hijackOk at Hhj
  iapply Hhj
  iintro %t %la %ra' %bw #Hca Hsend Hrecv Hfresh Hrdl HD
  icases Hrdl with ⟨%b, Hrdl, Hdis⟩
  wp_auto
  -- the head read: the connection's names, and the dialer's handshake written
  icases recvTok_proto (Gg := hG.goose_globalGS) cn true _ _ $$ Hrecv with ⟨Hrecv, #Hpp⟩
  icases req_of_read W a cn _ Hhs $$ Hpp with ⟨%γ, %L, #Hrpc, -, -⟩
  icases recvTok_keep_sentLb (Gg := hG.goose_globalGS) cn true false rfl _ _ $$ Hrecv
    with ⟨Hrecv, #Hsl⟩
  ihave #HP := hsAns_proto W a cn γ (W.hsAns a) (List.prefix_refl _) $$ [$Hrpc $Hsl]
  ihave #HP' : □ respProto (Gg := hG.goose_globalGS) W a cn ([] ++ connectAns) $$ []
  · rw [List.nil_append, ← HhsA]; iexact HP
  ihave #Hacc := write_acc (Gg := hG.goose_globalGS) cn true (respProto W a) [] connectAns $$ HP'
  ihave HwP := writeP_init (Gg := hG.goose_globalGS) cn true (respProto W a) [] $$ Hsend
  -- the answer, by one `Write` (its error not looked at)
  wp_apply wp_string_to_bytes as %sl ⟨Hsl, -⟩
  ihave Hsl : sl ↦* connectAns $$ [Hsl]
  · rw [show connectAns = go!"HTTP/1.0 " ++ connectedStatus ++ go!"\n\n" from rfl]; iexact Hsl
  wp_apply wp_Write t cn true a la ra' sl connectAns _ ed
      (writeP (Gg := hG.goose_globalGS) cn true (respProto W a) [])
      $$ [$Hca $Hsl $Hed $HwP $Hacc] as %nw0 %werr ⟨%w, %wres, HwP, Hsl, %Hw, -⟩
  obtain ⟨Hw, -⟩ := Hw
  iunfold writeP at HwP
  wp_apply wp_ServeConn s γs C W a t cn la ra' $$ [$Hsrv $Hserves $Henv $Hset $Hca HwP Hrecv Hfresh
      Hrdl Hdis Htok]
    as Htok
  · isplitr
    · ipureintro; exact Hb
    isplitr [Htok]
    · iunfold rpcAccepted
      iexists ([] ++ w)
      iframe HwP Hrecv Hfresh
      isplitr
      · ipureintro; rw [HhsA, List.nil_append]; exact Hw
      icases Hdis with (%Hb | #Hdead)
      · subst Hb; ileft; iexact Hrdl
      · iright; iexact Hdead
    iexact Htok
  iapply HΦ; iframe Htok HD

end proof

end net.rpc
end Perennial

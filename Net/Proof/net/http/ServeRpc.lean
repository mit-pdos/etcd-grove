/-
`http.Serve(l, nil)` on an rpc listener from `http.Serve`'s spec with a handler
(`Serve.specHandler`): what each address the listener takes gives a server with no handler
(`srvAddrH interface.nil`), from net/rpc's protocols at the listener (`rpcLisP`) and
`DefaultServeMux`'s route to an rpc handler (`muxRpc`).

* `respProto_prefixClosed`: the acceptor's rpc protocol is closed under prefixes.
* `rpc_headLaw`, `rpc_zLaw`: what the dialer writes past its `CONNECT` head was written after the
  acceptor's answer (`Z cn := sentLb cn true (W.hsAns a)`), which an acceptor that has written
  nothing has not written.
* `rpc_badReq`: Go's `400` answer is allowed (`hsErr connectAns`).
* `srvAddrH_nil_rpc`: `DefaultServeMux`'s `ServeHTTP` on the `CONNECT path` request
  (`wp_ServeMux_ServeHTTP_connect`) runs the rpc handler (`rpcHjHandler`).
-/
module

public import Net.Proof.net.http.MuxDefs

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.iris.style.nameCheck false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net

namespace net.http

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : net.http.Assumptions]
variable [π : NetProtoGS]

theorem respProto_prefixClosed (W : net.rpc.RpcWorld GF) (a : GoString) :
    ProtoPrefixClosed (net.rpc.respProto (Gg := hG.goose_globalGS) W a) where
  nil cn := by
    unfold net.rpc.respProto
    imodintro; iright; ipureintro; exact List.nil_prefix
  pre cn x y hxy := by
    unfold net.rpc.respProto
    iintro #H
    imodintro
    icases H with (⟨%γ, %Rs, #Hc, #Ha, %hok, #Hs⟩ | %h)
    · ileft
      iexists γ, Rs
      iframe Hc Ha
      isplitr
      · ipureintro; exact ⟨hok.1, hxy.trans hok.2⟩
      · icases Hs with (%h0 | #Hs)
        · ileft; ipureintro; subst h0; exact List.prefix_nil.mp hxy
        · iright; iexact Hs
    · iright; ipureintro; exact hxy.trans h

theorem rpc_headLaw (W : net.rpc.RpcWorld GF) (a path : GoString)
    (hhs : W.hs a = net.rpc.connectReq path) :
    ⊢ headLaw (net.rpc.reqProto (Gg := hG.goose_globalGS) W a) (net.rpc.connectReq path)
      (fun cn => sentLb (Gg := hG.goose_globalGS) cn true (W.hsAns a)) := by
  unfold headLaw net.rpc.reqProto
  imodintro
  iintro %cn %bs ⟨%γ, %L, -, -, -, Hor⟩
  icases Hor with (%h | H)
  · ileft; ipureintro; rw [← hhs]; exact h
  · iright; iexact H

theorem rpc_zLaw (W : net.rpc.RpcWorld GF) (a : GoString)
    (hans : W.hsAns a = net.rpc.connectAns) :
    ⊢ zLaw (fun cn => sentLb (Gg := hG.goose_globalGS) cn true (W.hsAns a))
      (net.rpc.respProto (Gg := hG.goose_globalGS) W a) := by
  unfold zLaw
  imodintro
  iintro %cn #Hlb Hs
  ihave %h := sendTok_sentLb_prefix (Gg := hG.goose_globalGS) cn true _ [] _ $$ Hs Hlb
  rw [hans] at h
  exact absurd (List.prefix_nil.mp h) (by decide)

theorem rpc_badReq (W : net.rpc.RpcWorld GF) (a : GoString) (cn : Nat)
    (hans : W.hsAns a = net.rpc.connectAns) :
    ⊢ net.rpc.respProto (Gg := hG.goose_globalGS) W a cn net.rpc.badReqAns := by
  unfold net.rpc.respProto
  iright; ipureintro
  rw [hans]; simp [net.rpc.hsErr]

/-- Each address an rpc listener takes gives `http.Serve(l, nil)` its handler's contract (see the
file header). -/
theorem srvAddrH_nil_rpc (wp_PathUnescape : net.url.PathUnescape.spec (GF := GF) (hG := hG))
    (wp_IndexByte : strings.IndexByte.spec (GF := GF) (hG := hG))
    (wp_Count : strings.Count.spec (GF := GF) (hG := hG))
    (wp_EscapedPath : net.url.URL.EscapedPath.spec (GF := GF) (hG := hG))
    (W : net.rpc.RpcWorld GF) (la path a : GoString) (hp : litPattern path)
    (ha : addrOk a = true ∧ lisAccepts la a) :
    isPkgInit (PROP := IProp GF) pkg_id.sync ∗ isPkgInit (PROP := IProp GF) pkg_id.net.url ∗
      isPkgInit (PROP := IProp GF) pkg_id.strings ∗
      net.rpc.rpcLisP (Gg := hG.goose_globalGS) W la (net.rpc.connectReq path) net.rpc.connectAns ∗
      muxRpc (GF := GF) (hG := hG) (globalAddr net.http.defaultServeMux) W
        (fun a => addrOk a = true ∧ lisAccepts la a) path ⊢
    srvAddrH (GF := GF) (interface.nil : GoInterface) a
      (net.rpc.reqProto (Gg := hG.goose_globalGS) W a)
      (net.rpc.respProto (Gg := hG.goose_globalGS) W a) path := by
  iintro ⟨#Hsync, #Hurl0, #Hstr, #Hlis, #Hmux⟩
  ihave #Hap := net.rpc.rpcLisP_addr (Gg := hG.goose_globalGS) W la _ _ a ha.1 ha.2 $$ Hlis
  iunfold net.rpc.rpcAddrP at Hap
  icases Hap with ⟨#Hproto, -, %hW⟩
  obtain ⟨hhs, hans⟩ := hW
  iunfold muxRpc at Hmux
  icases Hmux with ⟨%h, #Hrt, #Hrh⟩
  ihave #Hrpc := Hrh $$ %a %ha
  iunfold srvAddrH
  isplitr
  · ipureintro; exact respProto_prefixClosed W a
  isplitr
  · iexact Hproto
  isplitr
  · iexists _
    isplitr
    · iapply rpc_headLaw W a path hhs
    · iapply rpc_zLaw W a hans
  isplitr
  · imodintro; iintro %cn; iapply rpc_badReq W a cn hans
  imodintro
  iintro %cn
  iunfold connHandler
  iexists ⟨go.GoType.PointerType net.http.ServeMux.ty, #(globalAddr net.http.defaultServeMux)⟩
  isplitr
  · ipureintro; rfl
  imodintro
  iintro %rp %req %rv %u %m %cl %nb %ctx %ra %D %Φ ⟨%hrv, #Hhead, Hrest, Hu, -, Hhj, Htok⟩ HΦ
  subst hrv
  iunfold rpcHjHandler at Hrpc
  icases Hrpc with ⟨-, %e, %he, #Hsrv⟩
  iunfold reqHead at Hhead
  icases Hhead with ⟨#Hmeth, #Hra⟩
  iunfold reqRest at Hrest
  icases Hrest with ⟨Hurl, -, -, -, -, -, -, -, -, -, Hhost, -, -, -, -, Hruri, -, -, -, Hpat, -, Hpp,
    Hms, -⟩
  simp only [rrReqVal, connectReqVal]
  iunfold muxRoute at Hrt
  iapply (wp_ServeMux_ServeHTTP_connect wp_PathUnescape wp_IndexByte wp_Count wp_EscapedPath
    (globalAddr net.http.defaultServeMux) path h e he hp _ req u _ _ _ Φ)
  iframe Hsync Hurl0 Hstr Hrt Htok Hmeth Hruri Hurl Hhost Hpat Hpp Hms Hu
  iintro Htok
  iapply Hsrv $$ %cn %rp %req %D %(fun v => iprop(⌜v = #()⌝ ∗ Φ #())) [Hhj Htok]
  · iunfold reqHead
    rw [hhs]
    iframe Hhj Htok Hmeth Hra
  · inext
    iintro ⟨Htok, HD⟩
    isplitr
    · ipureintro; rfl
    · iapply HΦ; iframe Htok HD

end lemmas

end net.http
end Perennial

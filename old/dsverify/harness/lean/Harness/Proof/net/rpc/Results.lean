/-
The specs of the lab's `net/rpc` and `net/http` models (`notes/craq-net.md`, "rpc specs"), with
every hypothesis between the files discharged: what a run uses.

Client (`ClientDefs.lean`): `DialHTTP.wp` (a client of an rpc address, or an error),
`Client.Call.wp` (concurrent calls; nil: `Φ rep ""` of exactly one run of the method at the
server on the encoded arguments, the reply decoded; `ServerError(msg)`: `Φ rep msg` of exactly
one run, `msg ≠ ""`; any other error, not a `ServerError`: at most one run), `Client.Close.wp`.
Errors come with their `Error()` and the fact that their type implements `error` (`errMsg`,
`errAny`, `Defs.lean`); `wp_assert_serverErr` / `wp_assert_notServerErr` evaluate the comma-ok
assertion `err.(rpc.ServerError)`.

Server: `SetCodec.wp_proof` (`Codec.lean`), `RegisterName.wp_proof` and `Register.wp_proof`
(under the kit's `RpcNames`, with `kitNameOk`) (`ServerDefs.lean`),
`HandleHTTP.wp_proof` (`HandleHTTP.lean`, with the mux's owner token from
`net.http.muxOwner_claim`), and `rpc_ListenAndServe_pre` (below) for `ListenAndServe(a, nil)` on an rpc
address whose services the `DefaultServer` serves, which returns only with a listen error; each
request runs its method on the decoded arguments (`wp_ServeConn`, `Server.lean`); and
`rpc_Serve_pre` the same for `net.http.Serve.wp_proof`, `Serve(l, nil)` on a listener `l` of the
address (from `net.Listen`), which never returns.

Set-up: `rpcWorld_alloc`, `rpcAddr_set` (`Setup.lean`).
-/
module

public import Harness.Proof.net.rpc.Wire
public import Harness.Proof.net.rpc.Setup
public import Harness.Proof.net.rpc.HandleHTTP
public import Harness.Proof.net.rpc.HttpPath
public import Harness.Proof.net.rpc.Client
public import Harness.Proof.net.http.Serve

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode NetConn

namespace net.rpc

section results
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netConnExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [net.Assumptions] [net.model.Assumptions] [net.http.Assumptions] [net.rpc.Assumptions]
variable [RpcKit] [RpcCodec GF]

theorem Client.Call.wp : Client.Call.spec (GF := GF) (hG := hG) :=
  Client.Call.wp_proof getCodec.wp_proof writeFrame.wp_proof encodeMsg.wp_proof

theorem Client.input.wp : Client.input.spec (GF := GF) (hG := hG) :=
  Client.input.wp_proof getCodec.wp_proof readFrame.wp_proof decodeMsg.wp_proof

theorem newClient.wp : newClient.spec (GF := GF) (hG := hG) :=
  newClient.wp_proof Client.input.wp

theorem DialHTTPPath.wp : DialHTTPPath.spec (GF := GF) (hG := hG) :=
  DialHTTPPath.wp_proof readFull.wp_proof newClient.wp

theorem DialHTTP.wp : DialHTTP.spec (GF := GF) (hG := hG) :=
  DialHTTP.wp_proof DialHTTPPath.wp

theorem Client.Close.wp : Client.Close.spec (GF := GF) (hG := hG) :=
  Client.Close.wp_proof

/-- The `DefaultServer` (`s`) as the handler of `rpcPath` serves the rpc protocol of `a`. -/
theorem rpc_handlerOk (s : Loc) (W : RpcWorld GF) (a : GoString) :
    isPkgInit (PROP := IProp GF) pkg_id.net.rpc ∗ codecSet (GF := GF) ∗ kitCodecOk (GF := GF) ∗
        srvServes s W a ⊢
      net.http.handlerOk (serverHandler s) rpcPath (reqBodyProto W a) (respProto W a) :=
  srv_handlerOk lastDot.wp_proof readFrame.wp_proof writeFrame.wp_proof encodeMsg.wp_proof
    decodeMsg.wp_proof net.http.response.Hijack.wp_proof s W a

/-- What `ListenAndServe(a, nil)` (`net.http.ListenAndServe.wp_proof`, which returns only
with a listen error) needs on an rpc address `a` whose services the `DefaultServer` serves, after
`HandleHTTP` (its route): every request runs its method on the decoded arguments. -/
theorem rpc_ListenAndServe_pre (W : RpcWorld GF) (a : GoString) (s : Loc) :
    isPkgInit (PROP := IProp GF) pkg_id.net.rpc ∗ codecSet (GF := GF) ∗
        kitCodecOk (GF := GF) ∗ defaultServes W a ∗ globalAddr DefaultServer ↦□ s ∗
        net.http.muxRoute rpcPath (serverHandler s) ∗ addrTok a ∗ rpcAddr W a ⊢
      isPkgInit (PROP := IProp GF) pkg_id.net.http ∗ addrTok a ∗
        addrProto a (net.http.httpReqP rpcPath (reqBodyProto W a)) (respProto W a) ∗
        net.http.muxRoute rpcPath (serverHandler s) ∗
        net.http.handlerOk (serverHandler s) rpcPath (reqBodyProto W a) (respProto W a) ∗
        ⌜net.http.wfPath rpcPath⌝ := by
  iintro ⟨#Hpkg, #Hcs, #Hko, #Hds, #Hs, #Hr, Ht, Ha⟩
  ihave ⟨#Hhttp, -, -, -⟩ := deps_of_pkg $$ Hpkg
  unfold defaultServes
  icases Hds with ⟨%s', #Hs', #Hsv⟩
  icombine Hs Hs' gives %Heq
  subst Heq
  ihave #Hh := rpc_handlerOk s W a $$ [$Hpkg $Hcs $Hko $Hsv]
  unfold rpcAddr
  icases Ha with ⟨#Hp0, -⟩
  ihave #Hp : addrProto a (net.http.httpReqP rpcPath (reqBodyProto W a)) (respProto W a) $$ [Hp0]
  · unfold reqProto; iexact Hp0
  iframe Hhttp Ht Hp Hr Hh
  ipureintro; exact wfPath_rpcPath

/-- What `Serve(l, nil)` (`net.http.Serve.wp_proof`, which never returns) needs on a listener `l`
of an rpc address `a` whose services the `DefaultServer` serves, after `HandleHTTP` (its route):
every request runs its method on the decoded arguments. -/
theorem rpc_Serve_pre (W : RpcWorld GF) (a : GoString) (s l : Loc) (lid : w64) :
    isPkgInit (PROP := IProp GF) pkg_id.net.rpc ∗ codecSet (GF := GF) ∗
        kitCodecOk (GF := GF) ∗ defaultServes W a ∗ globalAddr DefaultServer ↦□ s ∗
        net.http.muxRoute rpcPath (serverHandler s) ∗ net.ownListener l lid a ∗ rpcAddr W a ⊢
      isPkgInit (PROP := IProp GF) pkg_id.net.http ∗ net.ownListener l lid a ∗
        addrProto a (net.http.httpReqP rpcPath (reqBodyProto W a)) (respProto W a) ∗
        net.http.muxRoute rpcPath (serverHandler s) ∗
        net.http.handlerOk (serverHandler s) rpcPath (reqBodyProto W a) (respProto W a) ∗
        ⌜net.http.wfPath rpcPath⌝ := by
  iintro ⟨#Hpkg, #Hcs, #Hko, #Hds, #Hs, #Hr, Hl, Ha⟩
  ihave ⟨#Hhttp, -, -, -⟩ := deps_of_pkg $$ Hpkg
  unfold defaultServes
  icases Hds with ⟨%s', #Hs', #Hsv⟩
  icombine Hs Hs' gives %Heq
  subst Heq
  ihave #Hh := rpc_handlerOk s W a $$ [$Hpkg $Hcs $Hko $Hsv]
  unfold rpcAddr
  icases Ha with ⟨#Hp0, -⟩
  ihave #Hp : addrProto a (net.http.httpReqP rpcPath (reqBodyProto W a)) (respProto W a) $$ [Hp0]
  · unfold reqProto; iexact Hp0
  iframe Hhttp Hl Hp Hr Hh
  ipureintro; exact wfPath_rpcPath

end results

end net.rpc

end Perennial

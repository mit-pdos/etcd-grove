/-
`http.Serve`'s spec on an rpc listener (`Net/Spec/net/http/Serve.lean`, `Serve.spec_rpc`), from
its spec with a handler (`Serve.specHandler`, the `nil` handler): each address the listener takes
gets `DefaultServeMux`'s contract from net/rpc's protocols at the listener and the mux's route to the
rpc handler (`ServeRpc.lean`, `srvAddrH_nil_rpc`). Until 2026-11-25 an interim trust-boundary
axiom. Lean-first.
-/
module

public import Net.Spec.net.http.Serve
public import Net.Spec.net.http.ServeHandler
public import Net.Proof.net.http.ServeRpc

@[expose] public section

noncomputable section

set_option linter.iris.style.nameCheck false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace net.http

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : net.http.Assumptions] [field_sem : net.FieldAssumptions]
variable [π : NetProtoGS]

theorem Serve.wp_proof_rpc (wp_ServeH : Serve.specHandler (GF := GF) (hG := hG))
    (wp_PathUnescape : net.url.PathUnescape.spec (GF := GF) (hG := hG))
    (wp_IndexByte : strings.IndexByte.spec (GF := GF) (hG := hG))
    (wp_Count : strings.Count.spec (GF := GF) (hG := hG))
    (wp_EscapedPath : net.url.URL.EscapedPath.spec (GF := GF) (hG := hG)) :
    Serve.spec_rpc (GF := GF) (hG := hG) := by
  intro W la path lis l hp hlen
  iintro %Φ ⟨%hb, #Hpkg, #Henv, #Hlp, #Hmux, Hlis, Hon, Hli, Htok⟩ HΦ
  ihave #Hctx : isPkgInit (PROP := IProp GF) pkg_id.context $$ []
  · iPkgInit
  ihave #Hlog : isPkgInit (PROP := IProp GF) pkg_id.log $$ []
  · iPkgInit
  ihave #Htime : isPkgInit (PROP := IProp GF) pkg_id.time $$ []
  · iPkgInit
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  ihave #Hatomic : isPkgInit (PROP := IProp GF) pkg_id.sync.atomic $$ []
  · iPkgInit
  ihave #Hurl : isPkgInit (PROP := IProp GF) pkg_id.net.url $$ []
  · iPkgInit
  ihave #Hstr : isPkgInit (PROP := IProp GF) pkg_id.strings $$ []
  · iPkgInit
  iunfold httpSrvEnv at Henv
  icases Henv with ⟨#He, #Hre, #Hse, #Hk, #Htm, #Hwp, #Hrp⟩
  iapply (wp_ServeH (interface.nil : GoInterface) lis l la
    (net.rpc.reqProto (Gg := hG.goose_globalGS) W) (net.rpc.respProto (Gg := hG.goose_globalGS) W)
    path hp hlen) $$ [Hlis Hon Hli]
  · iframe He Hre Hse Hctx Hlog Htime Hsync Hatomic Hk Hwp Hrp Htm Hlis Hon Hli
    imodintro
    iintro %a %ha
    iapply srvAddrH_nil_rpc wp_PathUnescape wp_IndexByte wp_Count wp_EscapedPath W la path a hp ha
    iframe Hsync Hurl Hstr Hlp Hmux
  · inext
    iintro %err -
    iapply HΦ
    iexact Htok

end proof

end net.http
end Perennial

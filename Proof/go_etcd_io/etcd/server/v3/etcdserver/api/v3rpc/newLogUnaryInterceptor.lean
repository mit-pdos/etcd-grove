/-
Proof of the spec of the same name (unit P3b). Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.newLogUnaryInterceptor
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__Logger
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.logUnaryRequestStats
public import Spec.google_golang_org.grpc.peer.FromContext
public import Spec.context.WithValueClientIP

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.api
  go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **The context the log interceptor derives is a run context** (PR etcd#22259): a `valueCtx`
at the key `ClientIPContextKey{}` over a run context answers every other key as its parent
(`context.WithValueClientIP.spec`), so the etcd keys other than the client IP's (nil), and the
peer, are the parent's; the client IP is the stored one. -/
theorem grpcRunCtx_withClientIP (ci c : GoInterfaceOk) (s : GoString) :
    grpcRunCtx (GF := GF) ci ∗ auth.ctxClientIPIs c (some s) ∗
      □ (∀ (k : GoInterfaceOk) (Φ : val → IProp GF),
          ⌜k.ty ≠ go_etcd_io.etcd.server.v3.auth.ClientIPContextKey.ty⌝ -∗
          WP (App (Val #(methods ci.ty go!"Value" ci.v)) (Val #(GoInterface.ok k))) {{ Φ }} -∗
          WP (App (Val #(methods c.ty go!"Value" c.v)) (Val #(GoInterface.ok k))) {{ Φ }}) ⊢
    grpcRunCtx c := by
  iintro ⟨#Hrc, #Hip, #Hdel⟩
  iunfold grpcRunCtx at Hrc
  icases Hrc with ⟨#H1, -, #Hpeer⟩
  iunfold grpcRunCtx
  isplitr
  · iintro !> %n %x %Φ %Hn %Hne HΦ
    ihave H2 := Hdel $$ %(⟨go.GoType.Named n [], x⟩ : GoInterfaceOk) %Φ %Hne
    iapply H2
    iapply H1 $$ %n %x %Φ %Hn %Hne HΦ
  isplitr
  · iexists (some s); iexact Hip
  iunfold grpcRunPeer at Hpeer
  icases Hpeer with ⟨%o, #Hpeer⟩
  iunfold grpcRunPeer
  iexists o
  iunfold grpcRunPeerIs at Hpeer
  iunfold grpcRunPeerIs
  iintro !> %Φ HΦ
  have Hne : google_golang_org.grpc.peer.peerKey.ty ≠
      go_etcd_io.etcd.server.v3.auth.ClientIPContextKey.ty := by
    unfold google_golang_org.grpc.peer.peerKey.ty go_etcd_io.etcd.server.v3.auth.ClientIPContextKey.ty
    simp
  ihave H2 := Hdel $$ %(⟨google_golang_org.grpc.peer.peerKey.ty,
    #(zero_val google_golang_org.grpc.peer.peerKey)⟩ : GoInterfaceOk) %Φ %Hne
  iapply H2
  iapply Hpeer $$ HΦ

/-- **The log interceptor's contract gives the transparent one** (and keeps itself): the
handler's continuation, given for any run context, is one for a run context with the client IP;
the peer is the run context's (`grpcRunPeer`). -/
theorem srvInterceptorOk_of_logIcStoresIP (ic : GoFunc) (R : IProp GF) (Q : GoInterface → IProp GF) :
    v3rpc.logIcStoresIP ic R Q ⊢ srvInterceptorOk ic R Q ∗ v3rpc.logIcStoresIP ic R Q := by
  iintro #Hstrong
  iframe Hstrong
  unfold srvInterceptorOk
  iintro !> %ci %cd %req %info %h %Ψ HR #Hctx #Hrc #Hinfo #HQ Hk
  ihave #Hrc' := Hrc
  iunfold grpcRunCtx at Hrc'
  icases Hrc' with ⟨-, -, #Hpeer⟩
  iunfold grpcRunPeer at Hpeer
  icases Hpeer with ⟨%o, #Hpeer⟩
  iunfold v3rpc.logIcStoresIP at Hstrong
  iapply Hstrong $$ %ci %cd %req %info %h %Ψ %o HR Hctx Hrc Hpeer Hinfo HQ
  isplit
  · icases Hk with ⟨Hk, -⟩
    iintro %ci' %cd' #Hctx' #Hrc' -
    iapply Hk $$ Hctx' Hrc'
  · icases Hk with ⟨-, Hk⟩
    iexact Hk

set_option hygiene false in
/-- The interceptor's tail after its context is fixed (`CI` at `CD`, a run context: `HCtx0`,
`HRc0`, with the client IP `HIP0`): the handler's call with it, `s.Logger()`, the deferred
`logUnaryRequestStats`. -/
local macro "log_tail" CI:term:max CD:term:max : tactic => `(tactic| (
  icases Hk with ⟨Hk, -⟩;
  ihave Hk := Hk $$ %$CI %$CD HCtx0 HRc0 HIP0;
  iunfold srvHandlerCall at Hk;
  wp_bind (App (App (Val #h) _) _);
  iapply (wp_wand (Φ := fun v => iprop(∃ resp err : GoInterface, ⌜v = PairV #resp #err⌝ ∗
    (srvLgReader s -∗ Ψ v)))) $$ Hk;
  iintro %v ⟨%resp, %err, %Hv, HΨ⟩;
  subst Hv;
  wp_auto;
  wp_apply wp_Logger s lg $$ [HR] as ⟨-, HR⟩;
  · iframe; iframe #; ipureintro; exact Hlgn
  wp_if_destruct;
  · exact absurd rfl Hlgn
  ihave #Hipok := ctxClientIPOk_of_runCtx $CI $$ HRc0;
  wp_apply wp_log $$ [];
  · iframe #; ipureintro; exact Hlgn
  iapply HΨ;
  iexact HR))

theorem v3rpc.newLogUnaryInterceptor.wp_proof
    (wp_Logger : EtcdServer.Logger.spec (GF := GF) (hG := hG))
    (wp_log : v3rpc.logUnaryRequestStats.spec (GF := GF) (hG := hG))
    (wp_FromContext : peer.FromContext.spec (GF := GF) (hG := hG))
    (wp_WithValue : context.WithValueClientIP.spec (GF := GF) (hG := hG)) :
    v3rpc.newLogUnaryInterceptor.spec (GF := GF) (hG := hG) := by
  intro s lg wd
  wp_start as ⟨#Hlg, %Hlgn, #Hwd⟩
  ihave #Ppeer : isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc.peer $$ []
  · iPkgInit
  ihave #Pctx : isPkgInit (PROP := IProp GF) pkg_id.context $$ []
  · iPkgInit
  wp_pures
  wp_alloc_auto
  irename : (s_ptr ↦ s : IProp GF) => Hs
  ipersist Hs
  wp_auto
  rw [recv_eq_func_mk]
  iapply HΦ
  iintro !> %Q
  iapply srvInterceptorOk_of_logIcStoresIP
  · iunfold v3rpc.logIcStoresIP
    iintro !> %ci %cd %req %info %h %Ψ %o HR #Hctx #Hrc #Hpeer #Hinfo #HQ Hk
    iunfold srvInterceptorCall
    wp_auto
    wp_apply wp_with_defer as %defer defer
    wp_apply time.wp_Now as %now -
    wp_apply (wp_FromContext ci o) $$ [] as %p %ok Hp
    · iframe #
    cases o with
    | none =>
      icases Hp with %Hok
      subst Hok
      wp_auto
      ihave #HCtx0 := Hctx
      ihave #HRc0 := Hrc
      ihave #HIP0 : iprop(True) $$ []
      · itrivial
      log_tail ci cd
    | some addr =>
      icases Hp with ⟨⟨%Hok, %Hpn⟩, #Hpi⟩
      subst Hok
      wp_auto
      rw [decide_eq_false Hpn]
      wp_auto
      iunfold grpcPeerIs at Hpi
      icases Hpi with ⟨%a, #Haddr, #Hstr⟩
      wp_auto
      wp_bind (App (Val #(methods a.ty go!"String" a.v)) _)
      iapply Hstr
      inext
      wp_auto
      wp_apply (wp_WithValue ci addr) $$ [] as %c ⟨#Hcctx, #Hcip, #Hdel⟩
      (try wp_auto)
      ihave #HCtx0 := Hcctx $$ %cd Hctx
      ihave #HRc0 := grpcRunCtx_withClientIP ci c addr $$ [Hrc Hcip Hdel]
      · iframe #
      ihave #HIP0 := Hcip
      log_tail c cd

end proof

end EtcdGrove
end Perennial

/-
The server loop of the lab's model of `net/http`: `serveConn` on an accepted connection of an
address whose dialers write `httpReqP p Pb`, with the default mux routing `p` to a handler that
meets `handlerOk`, and `ListenAndServe(a, nil)`, which serves each accepted connection in its own
goroutine and returns only when `Listen` fails, and `Serve(l, nil)`, the same loop on a listener
`l` the caller made, which never returns.
-/
module

public import Harness.Proof.net.http.Head
public import Harness.Proof.net.http.Handler
public import Harness.Proof.net.Listen
public import Harness.Proof.net.TCPListener__Accept
public import Harness.Proof.net.TCPConn__Close

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode NetConn

namespace net.http

section proofs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netConnExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [net.Assumptions] [net.model.Assumptions] [net.http.Assumptions]

set_option goose.wp.extras true

theorem muxRoute_global (p : GoString) (h : GoInterfaceOk) :
    muxRoute (GF := GF) p h ⊢ ∃ mux : Loc, globalAddr DefaultServeMux ↦□ mux := by
  unfold muxRoute defaultMux
  iintro ⟨%mux, %mp, %γ, ⟨#HD, -⟩, -⟩
  iexists mux; iexact HD

/-- `serveConn(c, nil)` on the acceptor's end `c` of a fresh connection whose dialers write
`httpReqP p Pb` and whose acceptor writes `Q`, with the default mux routing `p` to `h`: it reads
the head, gives `h` what `handlerOk` promises, and closes `c` unless `h` hijacked it. -/
abbrev serveConn.spec : Prop :=
  ∀ (c : Loc) (cid : w64) (p : GoString) (h : GoInterfaceOk) (Pb Q : Proto GF), wfPath p →
  {{ isPkgInit (PROP := IProp GF) pkg_id.net.http ∗ net.ownTCPConn c cid true ∗
      recvTok cid true (httpReqP p Pb) [] ∗ sendTok cid true Q [] ∗ connFresh cid true ∗
      muxRoute p h ∗ handlerOk h p Pb Q }}
    (App (App (Val (@! net.http.serveConn))
      (Val #(interface.mkOk (go.GoType.PointerType net.TCPConn.ty) #c))) (Val #interface.nil))
  {{ RET #(); True }}

theorem serveConn.wp_proof : serveConn.spec (GF := GF) (hG := hG) := by
  intro c cid p h Pb Q hp
  wp_start as ⟨#Hc, Hrecv, Hsend, Hf, #Hr, #Hh⟩
  ihave #Hnet := net_init_of_http $$ Hpkg
  wp_auto
  wp_apply readHead.wp_proof c cid p Pb hp $$ [$Hpkg $Hc $Hrecv] as %s %err Hres
  icases Hres with (⟨%Herr, Hs, Hrecv⟩ | ⟨%Herr, -⟩)
  rotate_left
  · cases err with
    | nil => exact absurd rfl Herr
    | ok i => ?_
    wp_auto
    wp_apply net.TCPConn.Close.wp_proof c cid true $$ [$Hnet $Hc] as %err2 -
    iapply HΦ; itrivial
  subst Herr
  wp_auto
  wp_apply parseRequestLine.wp_proof s (DFrac.own 1) p hp $$ Hs as Hs
  ihave ⟨%mux, #HD⟩ := muxRoute_global $$ Hr
  ihave #Hmh := mux_handlerOk mux p h Pb Q $$ HD Hr Hh
  wp_auto
  wp_bind (App (App (Val #(methods (go.GoType.PointerType net.http.ServeMux.ty) go!"ServeHTTP" #mux))
    (Val #(interface.mkOk (go.GoType.PointerType net.http.response.ty) #«$r0_ptr»))) (Val #«$a1_ptr»))
  unfold handlerOk
  iapply Hmh $$ Hpkg [«$r0»] «$a1» Hc Hrecv Hsend Hf
  · unfold respWriter
    iexists «$r0_ptr»
    iframe
    ipureintro; rfl
  inext
  iintro Hb
  unfold respWriterBack
  icases Hb with ⟨%l, %v, %Hl, Hv⟩
  simp [interface.mkOk] at Hl
  have Hl' := go.intoVal_inj Hl
  subst Hl'
  wp_auto
  rcases v.hijacked' with _ | _
  · wp_auto
    wp_apply net.TCPConn.Close.wp_proof c cid true $$ [$Hnet $Hc] as %err2 -
    iapply HΦ; itrivial
  · wp_auto
    iapply HΦ; itrivial

/-- `ListenAndServe(a, nil)` with the token of `a`, whose protocols are `httpReqP p Pb` (dialers)
and `Q` (acceptors), with the default mux routing the well-formed path `p` to `h`: it serves each
accepted connection in its own goroutine (`serveConn`), and returns only if `Listen` fails, with
that error and the token back. -/
abbrev ListenAndServe.spec : Prop :=
  ∀ (a p : GoString) (h : GoInterfaceOk) (Pb Q : Proto GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.net.http ∗ addrTok a ∗ addrProto a (httpReqP p Pb) Q ∗
      muxRoute p h ∗ handlerOk h p Pb Q ∗ ⌜wfPath p⌝ }}
    (App (App (Val (@! net.http.ListenAndServe)) (Val #a)) (Val #interface.nil))
  {{ (err : GoInterface), RET #err; ⌜err ≠ interface.nil⌝ ∗ addrTok a ∗
      ∃ code : w64, ⌜code ≠ errNone⌝ ∗ net.opErr go!"listen" code err }}

theorem ListenAndServe.wp_proof : ListenAndServe.spec (GF := GF) (hG := hG) := by
  intro a p h Pb Q
  wp_start as ⟨Htok, #Hpr, #Hr, #Hh, %hp⟩
  ihave #Hnet := net_init_of_http $$ Hpkg
  wp_auto
  wp_apply net.Listen.wp_proof a $$ [$Hnet $Htok] as %lv %err ⟨Htok, Hres⟩
  icases Hres with (⟨%l, %lid, %Hlv, #Hl⟩ | ⟨%i, %Hlv, Herr⟩) <;> obtain ⟨rfl, rfl⟩ := Hlv
  rotate_left
  · wp_auto
    iapply HΦ
    iframe
    ipureintro; exact fun h => nomatch h
  wp_auto
  wp_for
  wp_apply net.TCPListener.Accept.wp_proof l lid a (httpReqP p Pb) Q $$ [$Hnet $Hl $Hpr]
    as %cv %err Hres
  unfold net.newConnResult
  icases Hres with (⟨%c, %cid, %Hcv, #Hc, ⟨Hsend, Hrecv⟩, Hf⟩ | ⟨%i, %Hcv, -⟩) <;>
    obtain ⟨rfl, rfl⟩ := Hcv
  rotate_left
  · wp_auto
    wp_for_post
    iframe
  wp_auto
  wp_apply wp_fork $$ [Hsend Hrecv Hf]
  · wp_apply serveConn.wp_proof c cid p h Pb Q hp $$ [$Hpkg $Hc $Hsend $Hrecv $Hf $Hr $Hh]
    itrivial
  wp_for_post
  iframe

/-- `Serve(l, nil)` on a listener of `a` (from `net.Listen`), whose protocols are `httpReqP p Pb`
(dialers) and `Q` (acceptors), with the default mux routing the well-formed path `p` to `h`: it
serves each accepted connection in its own goroutine (`serveConn`) and never returns. -/
abbrev Serve.spec : Prop :=
  ∀ (l : Loc) (lid : w64) (a p : GoString) (h : GoInterfaceOk) (Pb Q : Proto GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.net.http ∗ net.ownListener l lid a ∗
      addrProto a (httpReqP p Pb) Q ∗ muxRoute p h ∗ handlerOk h p Pb Q ∗ ⌜wfPath p⌝ }}
    (App (App (Val (@! net.http.Serve))
      (Val #(interface.mkOk (go.GoType.PointerType net.TCPListener.ty) #l))) (Val #interface.nil))
  {{ (err : GoInterface), RET #err; False }}

theorem Serve.wp_proof : Serve.spec (GF := GF) (hG := hG) := by
  intro l lid a p h Pb Q
  wp_start as ⟨#Hl, #Hpr, #Hr, #Hh, %hp⟩
  ihave #Hnet := net_init_of_http $$ Hpkg
  wp_auto
  wp_for
  wp_apply net.TCPListener.Accept.wp_proof l lid a (httpReqP p Pb) Q $$ [$Hnet $Hl $Hpr]
    as %cv %err Hres
  unfold net.newConnResult
  icases Hres with (⟨%c, %cid, %Hcv, #Hc, ⟨Hsend, Hrecv⟩, Hf⟩ | ⟨%i, %Hcv, -⟩) <;>
    obtain ⟨rfl, rfl⟩ := Hcv
  rotate_left
  · wp_auto
    wp_for_post
    iframe
  wp_auto
  wp_apply wp_fork $$ [Hsend Hrecv Hf]
  · wp_apply serveConn.wp_proof c cid p h Pb Q hp $$ [$Hpkg $Hc $Hsend $Hrecv $Hf $Hr $Hh]
    itrivial
  wp_for_post
  iframe

end proofs

end net.http

end Perennial

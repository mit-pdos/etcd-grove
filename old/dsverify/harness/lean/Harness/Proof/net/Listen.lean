/-
The proof of `Spec/net/Listen.lean`: the model over `NetConn.wp_Listen_at` (`net.Listen.wp_at`), for
a configured address (`net.Listen.wp_proof`) and for a wildcard host (`net.ListenWild.wp_proof`).
-/
module

public import Harness.Spec.net.Listen

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode NetConn

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netConnExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [net.Assumptions] [net.model.Assumptions]

/-- `net.Listen(nw, addr)`, `nw` `"tcp"` or `"tcp4"`, binding the configured address `a`
(`NetConn.listenAddr`). -/
theorem net.Listen.wp_at_net (nw addr a : GoString) (hnw : net.tcpNet nw)
    (ha : a ∈ (netGS (G := hG.goose_globalGS)).addrs →
      listenAddr (netIp (L := hG.goose_localGS)) addr = a) :
  {{ isPkgInit (PROP := IProp GF) pkg_id.net ∗ addrTok (GF := GF) a }}
    (App (App (Val (@! net.Listen)) (Val #nw)) (Val #addr))
  {{ (lv err : GoInterface), RET (PairV #lv #err); addrTok a ∗
      ((∃ (l : Loc) (lid : w64),
          ⌜lv = interface.mkOk (go.GoType.PointerType net.TCPListener.ty) #l ∧
            err = interface.nil⌝ ∗ net.ownListener l lid a) ∨
       (∃ i, ⌜lv = interface.nil ∧ err = interface.ok i⌝ ∗
          ∃ code : w64, ⌜code ≠ errNone⌝ ∗ net.opErr go!"listen" code err)) }} := by
  wp_start as Htok
  wp_apply net.wp_tcpNetwork nw hnw
  wp_apply NetConn.wp_Listen_at addr a ha $$ Htok as %lid %code Hres
  wp_if_destruct
  · unfold listening
    icases Hres with ⟨#Hl, Htok⟩
    wp_apply net.wp_arbitraryAddr as %la %Hla
    wp_apply net.wp_newFD as %fd ⟨#Hfd, #Hlp, -⟩
    rw [net.TCPListener_ty_eq, net.Listener_ty_eq]
    wp_auto
    iapply wp_fupd
    wp_alloc l as Hl'
    iStructNamed Hl'
    ipersist fd
    wp_auto
    imodintro
    iapply HΦ
    iframe Htok
    ileft
    iexists l, lid
    isplitr
    · ipureintro; exact ⟨rfl, rfl⟩
    unfold net.ownListener net.listenerAddr
    iexists fd
    iframe fd Hfd Hl
    iexists la
    iframe Hlp
    ipureintro; exact Hla
  · wp_apply net.wp_codeErr as %inner Hinner
    wp_apply net.wp_maybeAddr as %ad -
    wp_apply net.wp_opError as %e ⟨#HOp, #HErr⟩
    iapply HΦ
    simp only [Hif, ↓reduceIte]
    iframe Hres
    iright
    iexists _
    isplitr
    · ipureintro; exact ⟨by trivial, rfl⟩
    iexists code
    isplitr
    · ipureintro; exact Hif
    unfold net.opErr
    iexists e, inner
    iframe HOp HErr Hinner
    ipureintro; rfl

/-- `net.Listen("tcp", addr)` binding the configured address `a` (`NetConn.listenAddr`). -/
theorem net.Listen.wp_at (addr a : GoString)
    (ha : a ∈ (netGS (G := hG.goose_globalGS)).addrs →
      listenAddr (netIp (L := hG.goose_localGS)) addr = a) :
  {{ isPkgInit (PROP := IProp GF) pkg_id.net ∗ addrTok (GF := GF) a }}
    (App (App (Val (@! net.Listen)) (Val #(go!"tcp"))) (Val #addr))
  {{ (lv err : GoInterface), RET (PairV #lv #err); addrTok a ∗
      ((∃ (l : Loc) (lid : w64),
          ⌜lv = interface.mkOk (go.GoType.PointerType net.TCPListener.ty) #l ∧
            err = interface.nil⌝ ∗ net.ownListener l lid a) ∨
       (∃ i, ⌜lv = interface.nil ∧ err = interface.ok i⌝ ∗
          ∃ code : w64, ⌜code ≠ errNone⌝ ∗ net.opErr go!"listen" code err)) }} :=
  net.Listen.wp_at_net go!"tcp" addr a net.tcpNet_tcp ha

theorem net.ListenNet.wp_proof : net.ListenNet.spec (GF := GF) (hG := hG) := fun nw a hnw =>
  net.Listen.wp_at_net nw a a hnw
    (fun hin => listenAddr_tame _ _ ((netGS (G := hG.goose_globalGS)).addrs_tame a hin))

theorem net.ListenWildNet.wp_proof : net.ListenWildNet.spec (GF := GF) (hG := hG) := by
  intro nw ip h port hnw hh
  iintro %Φ ⟨#Hpkg, %hip, Htok⟩ HΦ
  iapply net.Listen.wp_at_net nw (h ++ go!":" ++ port) (ip ++ go!":" ++ port) hnw
    (fun _ => by rw [listenAddr_wild _ h port hh, hip]) $$ [$Hpkg $Htok] HΦ

theorem net.Listen.wp_proof : net.Listen.spec (GF := GF) (hG := hG) := fun a =>
  net.Listen.wp_at a a (fun hin => listenAddr_tame _ _ ((netGS (G := hG.goose_globalGS)).addrs_tame a hin))

theorem net.ListenWild.wp_proof : net.ListenWild.spec (GF := GF) (hG := hG) := by
  intro ip h port hh
  iintro %Φ ⟨#Hpkg, %hip, Htok⟩ HΦ
  iapply net.Listen.wp_at (h ++ go!":" ++ port) (ip ++ go!":" ++ port)
    (fun _ => by rw [listenAddr_wild _ h port hh, hip]) $$ [$Hpkg $Htok] HΦ

end proof

end Perennial

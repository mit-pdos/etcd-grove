/-
The proof of `DialHTTPPath` (`Net/Spec/net/rpc/DialHTTPPath.lean`): `net.Dial` with the library's
`dial_au`, the connection registered in the world (`rpc_register`), the `CONNECT` request written
by `Conn.Write` (`writeP`, `write_acc`: a prefix of the dialer's handshake meets `reqProto`), the
answer read by `http.ReadResponse` over `bufio.NewReader` of the model's `connectReader` (a stream
reader, `connectReader.Read.spec`, whose bytes are a prefix of the answer and stay put after an
error: `crSt`, `crErr_final`); on the status `connected`, the reader has delivered the whole answer,
which the acceptor wrote only after the whole request (`respProto`'s `sentLb`), so the dialer has
written all of it (`sendTok_sentLb_prefix`): `rpcDialed`, then `NewClient`. Otherwise the error, an
`*OpError` (`errAny_opErrPtr`), after `Close`.
-/
module

public import Net.Spec.net.rpc.DialHTTPPath
public import Net.Spec.net.rpc.NewClient
public import Net.Spec.net.rpc.connectReader__Read
public import Net.Spec.net.Dial
public import Net.Spec.net.Conn__Write
public import Net.Spec.net.Conn__Close
public import Spec.bufio.NewReader
public import Net.Proof.net.rpc.ProtoGhost
public import Net.Proof.net.rpc.Errs

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
variable [π : NetProtoGS] [net.Assumptions] [_root_.Perennial.bufio.Assumptions]
variable [errors.Assumptions]

/-- A prefix of the dialer's handshake meets `reqProto`, before any request. -/
theorem hs_proto (W : RpcWorld GF) (a : GoString) (cn : Nat) (γ : RpcConnNames) (bs : List w8)
    (h : bs <+: W.hs a) :
    isRpcConn (Gg := hG.goose_globalGS) W a cn γ ∗ monoListLbOwn γ.reqs ([] : List RpcReq) ⊢
      □ reqProto (Gg := hG.goose_globalGS) W a cn bs := by
  iintro ⟨#Hrpc, #Hlb⟩
  imodintro
  iunfold reqProto
  iexists γ, []
  iframe Hrpc Hlb
  isplitr
  · ipureintro
    refine ⟨by simp, by simp, ?_⟩
    simpa [reqsWire] using h
  ileft; ipureintro; exact h

theorem DialHTTPPath.wp_proof (wp_Dial : net.Dial.spec (GF := GF) (hG := hG))
    (wp_Write : net.Conn.Write.spec (GF := GF) (hG := hG))
    (wp_Close : net.Conn.Close.spec (GF := GF) (hG := hG))
    (wp_NewReader : EtcdGrove.bufio.NewReader.spec (GF := GF) (hG := hG))
    (wp_crRead : connectReader.Read.spec (GF := GF) (hG := hG))
    (wp_ReadResponse : net.http.ReadResponse.spec (GF := GF) (hG := hG))
    (wp_NewClient : NewClient.spec (GF := GF) (hG := hG)) :
    DialHTTPPath.spec (GF := GF) (hG := hG) := by
  intro nw hnw W a path
  wp_start as ⟨%Hbound, #Henv, #Hhenv, #Hcon, #Haddr⟩
  iunfold rpcAddrP at Haddr
  icases Haddr with ⟨#Hap, #Hreg, ⟨%Hhs, %HhsA⟩⟩
  ihave %Hok := addrTok_ok $$ [Hap]
  · iapply addrProto_tok $$ Hap
  ihave #Henv' := Henv
  iunfold cliEnv at Henv'
  icases Henv' with ⟨%eof, %ueof, %ed, #Hio, #Hsync, #Heof, #Hueof, #Hed, #HefV, #HesV, #Hdbg⟩
  ihave #Hhenv' := Hhenv
  iunfold net.http.httpEnv at Hhenv'
  icases Hhenv' with ⟨#Hbufio, -⟩
  wp_auto
  wp_apply wp_Dial nw hnw a iprop(True)
      (fun cn => iprop(connEnd (Gg := hG.goose_globalGS) cn false (reqProto W a) (respProto W a)
        [] [] ∗ connFresh (Gg := hG.goose_globalGS) cn false)) $$ [Hap]
    as %c %err (⟨%Herr, %cn, #Hc, Hend, Hfresh⟩ | ⟨-, %x, -, #HE⟩)
  · isplitr
    · ipureintro; exact Hok
    isplit
    · itrivial
    · iapply dial_au $$ Hap
  · subst Herr
    iunfold net.isConn at Hc
    icases Hc with ⟨%t, %la, %ra, %Hct, #Hca⟩
    subst Hct
    iunfold connEnd at Hend
    icases Hend with ⟨Hsend, Hrecv⟩
    ihave #Hci := sendTok_connIs $$ Hsend
    ihave Hr : (|={⊤}=> ∃ γ : RpcConnNames, isRpcConn (Gg := hG.goose_globalGS) W a cn γ ∗
        monoListAuthOwn γ.reqs (1 : Qp).half ([] : List RpcReq) ∗
        ghostMapAuth γ.nm 1 (∅ : GMap Nat (GName × GName × GName)) : IProp GF) $$ [Hfresh]
    · iapply rpc_register (Gg := hG.goose_globalGS) W a cn $$ [$Hreg $Hfresh]
    imod Hr with ⟨%γ, #Hrpc, Hreqs, Hnm⟩
    imod monoListLbOwn_nil (GF := GF) (A := RpcReq) γ.reqs with #Hlb0
    wp_auto
    -- the `CONNECT` request: a prefix of the handshake is written
    wp_apply wp_string_to_bytes (go!"CONNECT " ++ path ++ go!" HTTP/1.0\n\n") as %sl ⟨Hsl, -⟩
    ihave #HP := hs_proto W a cn γ (connectReq path) (by rw [Hhs]; exact List.prefix_refl _) $$ [$Hrpc $Hlb0]
    ihave #HP' : □ reqProto (Gg := hG.goose_globalGS) W a cn ([] ++ connectReq path) $$ []
    · rw [List.nil_append]; iexact HP
    ihave #Hacc := write_acc (Gg := hG.goose_globalGS) cn false (reqProto W a) [] (connectReq path)
      $$ HP'
    ihave Hsl : sl ↦* connectReq path $$ [Hsl]
    · unfold connectReq; iexact Hsl
    ihave HwP := writeP_init (Gg := hG.goose_globalGS) cn false (reqProto W a) [] $$ Hsend
    wp_apply wp_Write t cn false a la ra sl (connectReq path) _ ed
        (writeP (Gg := hG.goose_globalGS) cn false (reqProto W a) [])
        $$ [$Hca $Hsl $Hed $HwP $Hacc] as %nw0 %werr ⟨%w, %wres, HwP, Hsl, %Hw, -⟩
    obtain ⟨Hw, -⟩ := Hw
    iunfold writeP at HwP
    simp only [List.nil_append]
    -- the reader: a `connectReader` of the connection, its once-cell, and a `bufio.Reader`
    wp_alloc cr as Hcr
    iStructNamed Hcr
    ipersist r
    imod mono_list_own_alloc (GF := GF) ([] : List (List w8)) with ⟨%γe, Hγe, -⟩
    ihave #Hcrat : crAt cr t cn a la ra $$ []
    · iunfold crAt; iframe r Hca
    ihave HS0 : crSt W a cn γ cr γe [] $$ [failed Hrecv Hreqs Hγe]
    · iunfold crSt
      iexists false, []
      iframe failed Hrecv Hrpc Hreqs
      isplitr
      · ipureintro; exact ⟨List.nil_prefix, Or.inl List.nil_prefix⟩
      iright
      iframe Hγe
      ipureintro; exact ⟨rfl, rfl⟩
    ihave #Hstream : EtcdGrove.io.readerStreamNE ⟨go.GoType.PointerType net.rpc.connectReader.ty, #cr⟩
        (crSt W a cn γ cr γe) (crErr γe) $$ []
    · iunfold EtcdGrove.io.readerStreamNE
      imodintro
      iintro %r0 %p %xs
      imodintro
      iintro %Φ' ⟨-, HS, Hp⟩ HΦ'
      wp_apply wp_crRead W a cn γ cr t la ra γe r0 p xs ed $$ [$Hio $Hed $Hcrat HS Hp]
        as %n %e ⟨%ys, %Hys, #He, Hp, HS⟩
      · iframe HS Hp; ipureintro; exact HhsA
      iapply HΦ'
      iexists ys
      iframe He Hp HS
      ipureintro; exact Hys
    have hty : (⟨go.GoType.PointerType net.rpc.connectReader.ty, #cr⟩ : GoInterfaceOk).ty ≠
        go.GoType.PointerType _root_.Perennial.bufio.Reader.ty := by
      simp only [ne_eq, go.GoType.PointerType.injEq]
      unfold net.rpc.connectReader.ty _root_.Perennial.bufio.Reader.ty
      simp
    ihave #Hstream0 := EtcdGrove.io.readerStreamNE_readerStream _ _ _ $$ Hstream
    ihave #Hbound : (□ ∀ r0, crSt W a cn γ cr γe r0 -∗ ⌜r0.length + 2 ^ 12 < 2 ^ 62⌝ : IProp GF) $$ []
    · imodintro
      iintro %r0 HS
      iunfold crSt at HS
      icases HS with ⟨%f, %R, -, -, -, -, ⟨%h1, %h2⟩, -⟩
      ipureintro
      have h4 : connectAns.length = 34 := by decide
      have h5 : badReqAns.length = 103 := by decide
      rcases h2 with h2 | h2
      · have h3 := (h1.trans h2).length_le; omega
      · have h3 := (h1.trans h2).length_le; omega
    wp_apply wp_NewReader ⟨go.GoType.PointerType net.rpc.connectReader.ty, #cr⟩
        (crSt W a cn γ cr γe) (crErr γe) [] hty $$ [$Hbufio $Hstream0 $Hbound $HS0] as %b Hb
    irename «$a1» => Hreq
    generalize «$a1_ptr» = req at *
    -- the laws `ReadResponse` takes of the stream
    ihave #Hlaw1 : (□ ∀ r0, crSt W a cn γ cr γe r0 -∗
        ⌜r0 <+: connectAns ∨ r0 <+: badReqAns⌝ : IProp GF) $$ []
    · imodintro
      iintro %r0 HS
      iunfold crSt at HS
      icases HS with ⟨%f, %R, -, -, -, -, ⟨%h1, %h2⟩, -⟩
      ipureintro; exact h2.imp h1.trans h1.trans
    ihave #Hlaw2 : (□ ∀ (r0 r' : List w8) (e : GoInterface), crErr γe r0 e -∗
        crSt W a cn γ cr γe r' -∗ ⌜r0 <+: r' → r' = r0⌝ : IProp GF) $$ []
    · imodintro
      iintro %r0 %r' %e He HS
      iapply crErr_final W a cn γ cr γe r0 r' e $$ [$He $HS]
    wp_apply wp_ReadResponse b _ (crSt W a cn γ cr γe) (crErr γe) req _
        $$ [$Hhenv $Hstream $Hb $Hlaw1 $Hlaw2 $Hreq] as %resp %rerr Hres
    · ipureintro; rfl
    icases Hres with (%Hne | ⟨%Hnil, %rv, Hrv, Hst⟩)
    · -- an error: wrapped
      cases rerr with
      | nil => exact absurd rfl Hne
      | ok ei =>
      wp_auto
      wp_apply wp_Close t cn false a la ra (fun _ => iprop(True)) $$ [$Hca] as %cerr -
      · imod close_au (Gg := hG.goose_globalGS) cn false $$ Hci with ⟨%st, %d, Hst, Hd, Hk⟩
        imodintro
        iexists st, d
        iframe Hst Hd
        iintro %res %st' %d' %Hco Hst' Hd'
        imod Hk $$ %res %st' %d' %Hco Hst' Hd' with -
        imodintro
        itrivial
      wp_alloc pe as Hpe
      wp_auto
      iapply HΦ
      iright
      isplitr
      · ipureintro; intro h; cases h
      iapply errAny_opErrPtr
    subst Hnil
    iStructNamed Hrv
    icases Hst with (%Hst | ⟨%Hst, Hb⟩)
    · -- another status: an error
      wp_auto
      rw [decide_eq_false Hst]
      wp_auto
      wp_apply wp_errors_New' as %x #Hx
      wp_apply wp_Close t cn false a la ra (fun _ => iprop(True)) $$ [$Hca] as %cerr -
      · imod close_au (Gg := hG.goose_globalGS) cn false $$ Hci with ⟨%st, %d, Hst, Hd, Hk⟩
        imodintro
        iexists st, d
        iframe Hst Hd
        iintro %res %st' %d' %Hco Hst' Hd'
        imod Hk $$ %res %st' %d' %Hco Hst' Hd' with -
        imodintro
        itrivial
      wp_alloc pe as Hpe
      wp_auto
      iapply HΦ
      iright
      isplitr
      · ipureintro; intro h; cases h
      iapply errAny_opErrPtr
    -- the answer: the reader delivered it whole
    wp_auto
    rw [decide_eq_true Hst]
    wp_auto
    ihave ⟨%q, HS, -⟩ := EtcdGrove.bufio.ownReader_open b _ _ _ connectAns $$ Hb
    iunfold crSt at HS
    icases HS with ⟨%f, %R, -, Hrecv, -, Hreqs, ⟨%h1, %h2⟩, -⟩
    have hR : R = connectAns := by
      have l1 := h1.length_le
      simp only [List.length_append] at l1
      rcases h2 with h2 | h2
      · have l2 := h2.length_le
        exact h2.eq_of_length (by omega)
      · exact absurd ((List.prefix_append _ _).trans h1 |>.trans h2) (by decide)
    subst hR
    icases recvTok_proto (Gg := hG.goose_globalGS) cn false _ _ $$ Hrecv with ⟨Hrecv, #Hpp⟩
    -- the acceptor wrote it after the dialer's whole request
    ihave #Hsl : sentLb (Gg := hG.goose_globalGS) cn false (W.hs a) $$ [Hpp]
    · iunfold protoPrefix at Hpp
      icases Hpp with (%Hnil | ⟨%ext, %Hext, #HP⟩)
      · exfalso; simp [connectAns] at Hnil
      iunfold respProto at HP
      icases HP with (⟨%γ', %Rs, -, -, -, (%He | #Hs)⟩ | %Herr)
      rotate_right
      · exfalso
        rw [HhsA, show hsErr connectAns = badReqAns from ite_eq_left rfl] at Herr
        exact absurd (Hext.trans Herr) (by decide)
      · exfalso
        subst He
        have := Hext.length_le
        simp [connectAns] at this
      · iexact Hs
    ihave %Hwhs := sendTok_sentLb_prefix (Gg := hG.goose_globalGS) cn false _ w (W.hs a) $$ HwP Hsl
    have hw : w = W.hs a := by
      rw [Hhs] at Hwhs ⊢
      exact (Hw.eq_of_length (Nat.le_antisymm Hw.length_le Hwhs.length_le)).symm ▸ rfl
    rw [hw]
    wp_apply wp_NewClient W a cn γ t la ra $$ [$Henv $Hca Hrpc Hreqs Hnm HwP Hrecv] as %cl Hcl
    · isplitr
      · ipureintro; exact Hbound
      iunfold rpcDialed
      rw [HhsA]
      iframe Hrpc Hreqs Hnm HwP Hrecv
    iapply HΦ
    ileft
    iframe Hcl
    ipureintro; rfl
  · ihave %Hnet := net.resErr_netErr _ _ _ _ _ _ _ $$ HE
    obtain ⟨-, Hne⟩ := Hnet
    have Hne' := Hne (by simp)
    obtain ⟨pe, rfl⟩ := Hne'
    wp_auto
    iapply HΦ
    iright
    isplitr
    · ipureintro; intro h; cases h
    iapply errAny_resErr $$ HE

end proof

end net.rpc
end Perennial

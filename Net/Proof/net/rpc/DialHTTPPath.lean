/-
The proof of `DialHTTPPath` (`Net/Spec/net/rpc/DialHTTPPath.lean`): `net.Dial` with the library's
`dial_rdl_au` (the dialer's read deadline not set), the connection registered in the world
(`rpc_register`), the `CONNECT` request written by `Conn.Write` (`writeP`, `write_acc`: a prefix of
the dialer's handshake meets `reqProto`), the answer read by `http.ReadResponse` over
`bufio.NewReader` of the connection (a stream reader, `crStream`, over `Conn.Read.specLc`: its bytes
are a prefix of the answer, `resp_before_req`, and after a read error it reads nothing more,
`read_dead_au` with the end's `rdlTok`, then `read_after_dead_au`: `crSt`, `crErr_final`); on the status `connected`, the reader has delivered the whole answer,
which the acceptor wrote only after the whole request (`respProto`'s `sentLb`), so the dialer has
written all of it (`sendTok_sentLb_prefix`): `rpcDialed`, then `NewClient`. Otherwise the error, an
`*OpError` after `Close`, proved `errPlain` (`DialHTTPPath.spec_plain`: `errPlain_opErrPtr`, its `Err`
`errLeaf` by `http.ReadResponse.spec_errs` over `crErr`'s `errLeaf`); `DialHTTPPath.spec` from it.
-/
module

public import Net.Spec.net.rpc.DialHTTPPath
public import Net.Spec.net.rpc.NewClient
public import Net.Spec.net.Conn__Read
public import Net.Proof.net.rpc.HttpDefs
public import GooseLang.Ext.Net.Stream
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
variable [package_sem' : net.rpc.Assumptions]
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

/-- A read error of the connection is a pointer (`io.ptrTyped`): `io.EOF`'s `*errorString`, or an
`*OpError`. -/
theorem readErr_ptr (r : ReadRes) (la ra ed err : GoInterface) (xe : Loc) :
    net.ReadErr (GF := GF) r (interface.mkOk errors.errorString.ty.PointerType #xe) la ra ed err ⊢
      ⌜_root_.Perennial.io.ptrTyped err⌝ := by
  cases r with
  | bytes bs =>
    simp only [net.ReadErr]
    iintro %h; subst h; ipureintro; exact _root_.Perennial.io.ptrTyped_nil
  | eof =>
    simp only [net.ReadErr]
    iintro %h; subst h; ipureintro
    intro ii T h hT
    simp only [interface.mkOk] at h
    cases h; exact ⟨xe, rfl⟩
  | err k =>
    simp only [net.ReadErr]
    iintro HE
    ihave %Hnet := net.resErr_netErr _ _ _ _ _ _ _ $$ HE
    obtain ⟨-, Hne⟩ := Hnet
    obtain ⟨pe, rfl⟩ := Hne (by simp)
    ipureintro
    intro ii T h hT
    simp only [interface.mkOk] at h
    cases h; exact ⟨pe, rfl⟩

/-- A read's error other than for bytes is a pointer: not `nil`, `errLeaf` (an `*errorString` or an
`*OpError`). -/
theorem readErr_some [errors.Assumptions] [fmt.Assumptions] [net.Assumptions] (r : ReadRes)
    (la ra ed err : GoInterface) (xe : Loc) (hr : ∀ bs, r ≠ .bytes bs) :
    net.ReadErr (GF := GF) r (interface.mkOk errors.errorString.ty.PointerType #xe) la ra ed err ⊢
      ⌜err ≠ interface.nil ∧ _root_.Perennial.io.ptrTyped err ∧ models_lab.errLeaf err⌝ := by
  cases r with
  | bytes bs => exact absurd rfl (hr bs)
  | eof =>
    simp only [net.ReadErr]
    iintro %h; subst h; ipureintro
    refine ⟨by simp [interface.mkOk], ?_, models_lab.errLeaf_ptr _ _ models_lab.noFmt_errorString⟩
    intro ii T h hT
    simp only [interface.mkOk] at h
    cases h; exact ⟨xe, rfl⟩
  | err k =>
    simp only [net.ReadErr]
    iintro HE
    ihave %Hnet := net.resErr_netErr _ _ _ _ _ _ _ $$ HE
    obtain ⟨-, Hne⟩ := Hnet
    obtain ⟨pe, rfl⟩ := Hne (by simp)
    ipureintro
    refine ⟨by simp [interface.mkOk], ?_, models_lab.errLeaf_ptr _ _ models_lab.noFmt_opError⟩
    intro ii T h hT
    simp only [interface.mkOk] at h
    cases h; exact ⟨pe, rfl⟩

/-- A read's error other than for bytes is a pointer, not `nil`, `errLeaf`, with an `Error()`
(`io.EOF`'s, or the `*OpError`'s: `resErr_errStr`). -/
theorem readErr_some' [fmt.Assumptions] (r : ReadRes) (la ra ed err : GoInterface) (xe : Loc) (m : GoString)
    (hr : ∀ bs, r ≠ .bytes bs) :
    (□ ∀ Φ : val → IProp GF, ▷ Φ #m -∗
      WP (App (Val #(methods (go.GoType.PointerType errors.errorString.ty) go!"Error" #xe))
        (Val #())) {{ Φ }}) -∗
    net.ReadErr (GF := GF) r (interface.mkOk errors.errorString.ty.PointerType #xe) la ra ed err -∗
      ⌜err ≠ interface.nil ∧ _root_.Perennial.io.ptrTyped err ∧ models_lab.errLeaf err⌝ ∗
        net.errStr err := by
  iintro #Hw HE
  ihave #Hes : net.errStr (GF := GF) err $$ [HE]
  · cases r with
    | bytes bs => exact absurd rfl (hr bs)
    | eof =>
      simp only [net.ReadErr]
      icases HE with %h; subst h
      iapply net.errStr_of_wp ⟨go.GoType.PointerType errors.errorString.ty, #xe⟩ m $$ Hw
    | err k =>
      simp only [net.ReadErr]
      iapply net.resErr_errStr $$ HE
  ihave %H := readErr_some r la ra ed err xe hr $$ HE
  iframe Hes
  ipureintro; exact H

/-- A reader with its protocol fact back. -/
theorem recvTokL_back (cn : Nat) (s : Bool) (P : Proto GF) (R : List w8) :
    recvTokL (Gg := hG.goose_globalGS) cn s P R ∗ protoPrefix P cn R ⊢
      recvTok (Gg := hG.goose_globalGS) cn s P R := by
  unfold recvTokL recvTok
  iintro ⟨⟨H, -⟩, #Hp⟩
  iframe H Hp

/-- The dialer's end of `cn`, before any request, is a stream reader that makes progress over
`crSt` (`HttpDefs.lean`): its bytes extend the answer read so far, a prefix of the answer or of
the `400` answer (`resp_before_req`, with the call's credit); a read that fails (EOF, a `sys` error
or `closed`: no timeout, the read deadline not set) makes the end's reading dead (`read_dead_au`),
recorded in `γe`, and every later read returns no byte (`read_after_dead_au`). -/
theorem crStream (wp_Read : net.Conn.Read.specLc (GF := GF) (hG := hG))
    (W : RpcWorld GF) (a : GoString) (cn : Nat) (γ : RpcConnNames) (t : Loc) (la ra : GoInterface)
    (γe : GName) (ed : GoInterface) (hA : W.hsAns a = connectAns) :
    isPkgInit (PROP := IProp GF) pkg_id.io ∗ isPkgInit (PROP := IProp GF) pkg_id.internal.poll ∗
      globalAddr internal.poll.ErrDeadlineExceeded ↦□ ed ∗ net.connAt (GF := GF) t cn false a la ra ⊢
    EtcdGrove.io.readerStreamNE ⟨go.GoType.PointerType net.TCPConn.ty, #t⟩ (crSt W a cn γ γe)
      (crErr γe) := by
  iintro ⟨#Hio, #Hpoll, #Hed, #Hconn⟩
  ihave #Hinit := _root_.Perennial.io.isInit_access $$ Hio
  icases Hinit with ⟨-, -, -, -, #HEOF, -, -⟩
  unfold errors.newVar
  icases HEOF with ⟨%xe, #Hxe, -, #Hxew⟩
  iunfold EtcdGrove.io.readerStreamNE
  imodintro
  iintro %r %p %xs
  imodintro
  iintro %Φ ⟨-, Hst, Hp⟩ HΦ
  iunfold crSt at Hst
  icases Hst with ⟨Hrecv, Hrdl, #Hrpc, Hh, %Hpre, Hc⟩
  ihave %Hlen := ownSlice_len $$ Hp
  have hxl : xs.length = p.len.toNat := by
    rw [Hlen.1]; have := Hlen.2; unfold sint.nat; word
  icases recvTok_proto (Gg := hG.goose_globalGS) cn false _ _ $$ Hrecv with ⟨Hrecv, #Hpp0⟩
  ihave HrL := recvTok_L (Gg := hG.goose_globalGS) cn false _ _ $$ Hrecv
  iapply wp_fupd
  icases Hc with (⟨Hc, #Hdead⟩ | Hc)
  · -- failed before: no byte
    wp_apply wp_Read t cn false a la ra p xs (interface.mkOk errors.errorString.ty.PointerType #xe) ed
        (fun res => iprop(recvTokL (Gg := hG.goose_globalGS) cn false (respProto W a) r ∗
          ⌜res.got = [] ∧ (p.len.toNat ≠ 0 → ∀ bs, res ≠ .bytes bs)⌝)) $$ [Hp HrL]
      as %k %err ⟨%res, %bs', ⟨HrL, %Hres⟩, Hp, %Hout, HE, -⟩
    · (try iframe Hio); (try iframe Hpoll); iframe Hconn Hp Hxe Hed
      imod read_after_dead_au (Gg := hG.goose_globalGS) cn false _ _ p.len.toNat $$ [$HrL $Hdead]
        with ⟨%st, %d, HE, HD, Hcl⟩
      imodintro
      iexists st, d
      iframe HE HD
      iintro %r' %d' %Hrd HE HD
      iapply Hcl $$ %r' %d' %Hrd HE HD
    ihave HrT := recvTokL_back cn false _ _ $$ [$HrL $Hpp0]
    imod monoListAuthOwn_update (GF := GF) [r] (List.prefix_refl _) $$ Hc with ⟨Hc, #Hlb⟩
    rcases res with bs | _ | k0
    · -- `(0, nil)` on an empty buffer
      obtain ⟨hk, rfl⟩ := Hout
      obtain ⟨hg, hne⟩ := Hres
      simp only [ReadRes.got] at hg
      subst hg
      have hx0 : p.len.toNat = 0 := by
        rcases Nat.eq_zero_or_pos p.len.toNat with h | h
        · exact h
        · exact absurd rfl (hne (by omega) [])
      have hxs : xs = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst hxs
      imodintro
      iapply HΦ
      iexists []
      simp only [List.append_nil, List.length_nil, List.drop_zero, List.nil_append, List.take_nil]
      iframe Hp
      isplitr
      · ipureintro
        refine ⟨?_, by simp, fun h => absurd rfl h⟩
        simpa using hk
      isplitl [HE]
      · try simp only [net.ReadErr]
        icases HE with %h; subst h
        iapply EtcdGrove.io.errAt_nil
      iunfold crSt
      iframe HrT Hrdl Hrpc Hh
      isplitr
      · ipureintro; exact Hpre
      ileft; iframe Hc Hdead
    all_goals (
      obtain ⟨hk, rfl⟩ := Hout
      ihave ⟨%Hne, #Hes⟩ := readErr_some' _ la ra ed err xe _ (by intro bs h; cases h) $$ Hxew HE
      obtain ⟨Hne, Hptr, Hlf⟩ := Hne
      imodintro
      iapply HΦ
      iexists []
      simp only [List.append_nil, List.length_nil, List.drop_zero, List.nil_append]
      iframe Hp
      isplitr
      · ipureintro
        exact ⟨by rw [hk]; rfl, by simp, fun _ => Or.inr Hne⟩
      isplitr
      · unfold EtcdGrove.io.errAt
        isplitl []
        · iright; imodintro; iunfold crErr; iframe Hlb Hes; ipureintro; exact Hlf
        · ipureintro; exact Hptr
      iunfold crSt
      iframe HrT Hrdl Hrpc Hh
      isplitr
      · ipureintro; exact Hpre
      ileft; iframe Hc Hdead)
  · -- not failed: read into `p`
    wp_apply wp_Read t cn false a la ra p xs (interface.mkOk errors.errorString.ty.PointerType #xe) ed
        (fun res => iprop(recvTokL (Gg := hG.goose_globalGS) cn false (respProto W a) (r ++ res.got) ∗
          rdlTok (Gg := hG.goose_globalGS) cn false false ∗
          ⌜∃ st d d', st.rdl = false ∧ ReadOutcome st d p.len.toNat res d'⌝ ∗
          (⌜res = .eof ∨ res = .err .sys ∨ res = .err .closed⌝ -∗
            readDead (Gg := hG.goose_globalGS) cn false))) $$ [Hp HrL Hrdl]
      as %k %err ⟨%res, %bs', ⟨HrL, Hrdl, %Hro, Hdead⟩, Hp, %Hout, HE, Hlc1, Hlc2⟩
    · (try iframe Hio); (try iframe Hpoll); iframe Hconn Hp Hxe Hed
      imod read_dead_au (Gg := hG.goose_globalGS) cn false _ _ p.len.toNat false $$ [$HrL $Hrdl]
        with ⟨%st, %d, HE, HD, Hcl⟩
      imodintro
      iexists st, d
      iframe HE HD
      iintro %r' %d' %Hrd HE HD
      iapply Hcl $$ %r' %d' %Hrd HE HD
    obtain ⟨st, d, d', hrdl, Hro⟩ := Hro
    have Hgl := readOutcome_got_le Hro
    ihave HrT := recvTokL_later (Gg := hG.goose_globalGS) cn false _ _ $$ HrL
    imod lc_fupd_elim_later (E := ⊤) $$ Hlc1 HrT with HrT
    icases recvTok_proto (Gg := hG.goose_globalGS) cn false _ _ $$ HrT with ⟨HrT, #Hpp⟩
    imod resp_before_req W a cn γ _ $$ [$Hrpc $Hh $Hlc2 $Hpp] with ⟨Hh, %Hpre'⟩
    rw [hA, show hsErr connectAns = badReqAns from ite_eq_left rfl] at Hpre'
    rcases res with bs | _ | (_ | _ | _)
    · -- bytes: no error
      simp only [net.ReadErr]
      icases HE with %Herr
      subst Herr
      obtain ⟨hk, rfl⟩ := Hout
      simp only [ReadRes.got] at Hgl Hpre' ⊢
      have hbl : bs.length ≤ xs.length := by rw [hxl]; exact Hgl.1
      imodintro
      iapply HΦ
      iexists bs
      rw [List.take_of_length_le hbl]
      iframe Hp
      isplitr
      · ipureintro
        refine ⟨?_, hbl, fun hx => Or.inl ?_⟩
        · rw [Nat.min_eq_right hbl] at hk; exact hk
        · rintro rfl
          have := Hgl.2 rfl
          exact hx (List.eq_nil_of_length_eq_zero (by omega))
      isplitr
      · iapply EtcdGrove.io.errAt_nil
      iunfold crSt
      iframe HrT Hrdl Hrpc Hh Hc
      ipureintro; exact Hpre'
    all_goals (
      obtain ⟨hk, rfl⟩ := Hout
      simp only [ReadRes.got, List.append_nil] at Hpre' ⊢
      ihave ⟨%Hne, #Hes⟩ := readErr_some' _ la ra ed err xe _ (by intro bs h; cases h) $$ Hxew HE
      obtain ⟨Hne, Hptr, Hlf⟩ := Hne
      ihave #Hd : readDead (Gg := hG.goose_globalGS) cn false $$ [Hdead]
      · iapply Hdead
        ipureintro
        first
        | exact absurd Hro (fun h => readOutcome_no_timeout hrdl h)
        | simp
      imod monoListAuthOwn_update_app (GF := GF) [r] $$ Hc with ⟨Hc, #Hlb⟩
      simp only [List.nil_append]
      imodintro
      iapply HΦ
      iexists []
      simp only [List.append_nil, List.length_nil, List.drop_zero, List.nil_append]
      iframe Hp
      isplitr
      · ipureintro
        exact ⟨by rw [hk]; rfl, by simp, fun _ => Or.inr Hne⟩
      isplitr
      · unfold EtcdGrove.io.errAt
        isplitl []
        · iright; imodintro; iunfold crErr; iframe Hlb Hes; ipureintro; exact Hlf
        · ipureintro; exact Hptr
      iunfold crSt
      iframe HrT Hrdl Hrpc Hh
      isplitr
      · ipureintro; exact Hpre'
      ileft; iframe Hc Hd)

theorem DialHTTPPath.wp_proof_plain (wp_Dial : net.Dial.spec (GF := GF) (hG := hG))
    (wp_Write : net.Conn.Write.spec (GF := GF) (hG := hG))
    (wp_Close : net.Conn.Close.spec (GF := GF) (hG := hG))
    (wp_NewReader : EtcdGrove.bufio.NewReader.spec (GF := GF) (hG := hG))
    (wp_ReadLc : net.Conn.Read.specLc (GF := GF) (hG := hG))
    (wp_ReadResponse : net.http.ReadResponse.spec_errs (GF := GF) (hG := hG))
    (wp_NewClient : NewClient.spec (GF := GF) (hG := hG)) :
    DialHTTPPath.spec_plain (GF := GF) (hG := hG) := by
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
  icases Hhenv' with ⟨#Hbufio, -, #Hfmt, -⟩
  -- `Conn.Read` takes `internal/poll`'s package fact: `net`'s (a precondition) imports it
  ihave #Hpoll : isPkgInit (PROP := IProp GF) pkg_id.internal.poll $$ []
  · solve_pkg_init
  ihave #Hsys := net.errnoOk_of_poll $$ Hpoll
  wp_auto
  wp_apply wp_Dial nw hnw a iprop(True)
      (fun cn => iprop(connEnd (Gg := hG.goose_globalGS) cn false (reqProto W a) (respProto W a)
        [] [] ∗ connFresh (Gg := hG.goose_globalGS) cn false ∗
        rdlTok (Gg := hG.goose_globalGS) cn false false)) $$ [Hap]
    as %c %err (⟨%Herr, %cn, #Hc, Hend, Hfresh, Hrdl⟩ | ⟨-, %x, #Hx, #HE⟩)
  · isplitr
    · ipureintro; exact Hok
    isplit
    · itrivial
    · iapply dial_rdl_au $$ Hap
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
        $$ [$Hpoll $Hca $Hsl $Hed $HwP $Hacc] as %nw0 %werr ⟨%w, %wres, HwP, Hsl, %Hw, -⟩
    obtain ⟨Hw, -⟩ := Hw
    iunfold writeP at HwP
    simp only [List.nil_append]
    -- the reader: a `bufio.Reader` of the connection, the once-cell of its failure
    imod mono_list_own_alloc (GF := GF) ([] : List (List w8)) with ⟨%γe, Hγe, -⟩
    ihave HS0 : crSt W a cn γ γe [] $$ [Hrecv Hrdl Hreqs Hγe]
    · iunfold crSt
      iframe Hrecv Hrdl Hrpc Hreqs Hγe
      ipureintro; exact Or.inl List.nil_prefix
    ihave #Hstream := crStream wp_ReadLc W a cn γ t la ra γe ed HhsA $$ [$Hio $Hpoll $Hed $Hca]
    have hty : (⟨go.GoType.PointerType net.TCPConn.ty, #t⟩ : GoInterfaceOk).ty ≠
        go.GoType.PointerType _root_.Perennial.bufio.Reader.ty := by
      simp only [ne_eq, go.GoType.PointerType.injEq]
      unfold net.TCPConn.ty _root_.Perennial.bufio.Reader.ty
      simp
    ihave #Hstream0 := EtcdGrove.io.readerStreamNE_readerStream _ _ _ $$ Hstream
    ihave #Hbound : (□ ∀ r0, crSt W a cn γ γe r0 -∗ ⌜r0.length + 2 ^ 12 < 2 ^ 62⌝ : IProp GF) $$ []
    · imodintro
      iintro %r0 HS
      iunfold crSt at HS
      icases HS with ⟨-, -, -, -, %h2, -⟩
      ipureintro
      have h4 : connectAns.length = 34 := by decide
      have h5 : badReqAns.length = 103 := by decide
      rcases h2 with h2 | h2
      · have h3 := h2.length_le; omega
      · have h3 := h2.length_le; omega
    wp_apply wp_NewReader ⟨go.GoType.PointerType net.TCPConn.ty, #t⟩
        (crSt W a cn γ γe) (crErr γe) [] hty $$ [$Hbufio $Hstream0 $Hbound $HS0] as %b Hb
    irename «$a1» => Hreq
    generalize «$a1_ptr» = req at *
    -- the laws `ReadResponse` takes of the stream
    ihave #Hlaw1 : (□ ∀ r0, crSt W a cn γ γe r0 -∗
        ⌜r0 <+: connectAns ∨ r0 <+: badReqAns⌝ : IProp GF) $$ []
    · imodintro
      iintro %r0 HS
      iunfold crSt at HS
      icases HS with ⟨-, -, -, -, %h2, -⟩
      ipureintro; exact h2
    ihave #Hlaw2 : (□ ∀ (r0 r' : List w8) (e : GoInterface), crErr γe r0 e -∗
        crSt W a cn γ γe r' -∗ ⌜r0 <+: r' → r' = r0⌝ : IProp GF) $$ []
    · imodintro
      iintro %r0 %r' %e He HS
      iapply crErr_final W a cn γ γe r0 r' e $$ [$He $HS]
    ihave #Hlaw3 : (□ ∀ (r0 : List w8) (e : GoInterface), crErr γe r0 e -∗
        net.errStr e : IProp GF) $$ []
    · imodintro
      iintro %r0 %e He
      iunfold crErr at He
      icases He with ⟨-, #Hes, -⟩
      iexact Hes
    ihave #Hlaw4 : (□ ∀ (r0 : List w8) (e : GoInterface), crErr γe r0 e -∗
        ⌜models_lab.errLeaf e⌝ : IProp GF) $$ []
    · imodintro
      iintro %r0 %e He
      iunfold crErr at He
      icases He with ⟨-, -, %Hl⟩
      ipureintro; exact Hl
    wp_apply wp_ReadResponse models_lab.errLeaf (fun _ h => h) b _ (crSt W a cn γ γe) (crErr γe)
        req _ $$ [$Hhenv $Hstream $Hb $Hlaw1 $Hlaw2 $Hlaw3 $Hreq $Hlaw4] as %resp %rerr Hres
    · ipureintro; rfl
    icases Hres with (⟨⟨%Hne, %Hlf⟩, #Hrm⟩ | ⟨%Hnil, %rv, Hrv, Hst⟩)
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
      ipersist Hpe
      wp_auto
      iapply HΦ
      iright
      isplitr
      · ipureintro; intro h; cases h
      iapply errPlain_opErrPtr $$ Hpe Hsys
      all_goals try (first
        | exact ⟨models_lab.errLeaf_nil, models_lab.errLeaf_nil, Hlf⟩
        | exact ⟨models_lab.errLeaf_nil, models_lab.errLeaf_nil,
            models_lab.errLeaf_ptr _ _ models_lab.noFmt_errorString⟩)
      unfold net.opErrMsgOk net.addrOrNil
      isplitr
      · iexact Hrm
      isplitr <;> (ileft; ipureintro; rfl)
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
      ipersist Hpe
      wp_auto
      iapply HΦ
      iright
      isplitr
      · ipureintro; intro h; cases h
      iapply errPlain_opErrPtr $$ Hpe Hsys
      all_goals try (first
        | exact ⟨models_lab.errLeaf_nil, models_lab.errLeaf_nil, Hlf⟩
        | exact ⟨models_lab.errLeaf_nil, models_lab.errLeaf_nil,
            models_lab.errLeaf_ptr _ _ models_lab.noFmt_errorString⟩)
      unfold net.opErrMsgOk net.addrOrNil
      isplitr
      · iapply net.errStr_of_wp ⟨go.GoType.PointerType errors.errorString.ty, #x⟩ _ $$ Hx
      isplitr <;> (ileft; ipureintro; rfl)
    -- the answer: the reader delivered it whole
    wp_auto
    rw [decide_eq_true Hst]
    wp_auto
    ihave ⟨%q, HS, -⟩ := EtcdGrove.bufio.ownReader_open b _ _ _ connectAns $$ Hb
    iunfold crSt at HS
    icases HS with ⟨Hrecv, -, -, Hreqs, %h2, -⟩
    have hq : connectAns ++ q = connectAns := by
      rcases h2 with h2 | h2
      · have l := h2.length_le
        simp only [List.length_append] at l
        rw [List.eq_nil_of_length_eq_zero (by omega : q.length = 0), List.append_nil]
      · exact absurd ((List.prefix_append _ _).trans h2) (by decide)
    rw [hq]
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
    iapply errPlain_resErr _ _ _ _ _ _ _ $$ [$Hsys $HE]
    iintro %ed' %Hed'
    cases Hed'

/-- `DialHTTPPath.spec`, from `DialHTTPPath.spec_plain` (`errPlain` gives `errAny`). -/
theorem DialHTTPPath.wp_proof (wp_Dial : net.Dial.spec (GF := GF) (hG := hG))
    (wp_Write : net.Conn.Write.spec (GF := GF) (hG := hG))
    (wp_Close : net.Conn.Close.spec (GF := GF) (hG := hG))
    (wp_NewReader : EtcdGrove.bufio.NewReader.spec (GF := GF) (hG := hG))
    (wp_ReadLc : net.Conn.Read.specLc (GF := GF) (hG := hG))
    (wp_ReadResponse : net.http.ReadResponse.spec_errs (GF := GF) (hG := hG))
    (wp_NewClient : NewClient.spec (GF := GF) (hG := hG)) :
    DialHTTPPath.spec (GF := GF) (hG := hG) := by
  intro nw hnw W a path
  wp_start_folded as Hpre
  wp_apply DialHTTPPath.wp_proof_plain wp_Dial wp_Write wp_Close wp_NewReader wp_ReadLc
      wp_ReadResponse wp_NewClient nw hnw W a path $$ Hpre as %c %err Hres
  iapply HΦ
  icases Hres with (H1 | ⟨%Hne, #Hp⟩)
  · ileft; iexact H1
  · iright
    isplitr
    · ipureintro; exact Hne
    iapply models_lab.errPlain_errAny $$ Hp

end proof

end net.rpc
end Perennial

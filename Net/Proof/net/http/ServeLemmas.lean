/-
Lemmas for `conn.serve`'s proof (`Net/Proof/net/http/conn__serve.lean`): what it needs of
`readRequest`'s errors (`reqErr (crHeadErr γe)`: never `errTooLarge`, never an
`*unsupportedTEError`, never a `statusError`), and its small callees on a server `http.Serve` made
(`srvServe`, `srvDflt`).
-/
module

public import Net.Proof.net.http.ServeDefs
public import Net.Proof.net.http.ConnReaderHead
public import Net.Proof.net.http.ServerConnLemmas
public import Net.Spec.net.OpError__Timeout
public import Perennial.Proof.fmt.DoPrintf
public import Perennial.Spec.fmt.newPrinter
public import Perennial.Spec.fmt.buffer__writeString
public import Perennial.Spec.fmt.pp__free
public import Perennial.Spec.internal.gomodel.Choose
public import Net.Spec.net.Conn__Close

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace net.http

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [package_sem' : net.http.Assumptions]
variable [π : NetProtoGS]

/-- The dynamic types of `readRequest`'s errors: an `*errorString`, a `textproto.ProtocolError` or
an `*OpError`. -/
theorem reqErr_shape (γe : GName) (err : GoInterface) :
    reqErr (crHeadErr (GF := GF) γe) err ⊢
      ⌜(∃ x : Loc, err = interface.mkOk (go.GoType.PointerType errors.errorString.ty) #x) ∨
        (∃ msg : GoString, err = interface.mkOk net.textproto.ProtocolError.ty #msg) ∨
        (∃ pe : Loc, err = interface.mkOk (go.GoType.PointerType net.OpError.ty) #pe)⌝ := by
  iintro #H
  iunfold reqErr at H
  icases H with (H | ⟨%x, %hx, -⟩ | ⟨%x, %s, %hx, -⟩)
  · iunfold mimeErr at H
    icases H with (⟨%r, #H⟩ | %h)
    · iunfold crHeadErr at H
      icases H with ⟨-, -, H⟩
      iunfold crErrId at H
      icases H with (⟨%xe, %hx, -⟩ | ⟨%src, %addr, %e', H, -⟩)
      · ipureintro; exact .inl ⟨xe, hx⟩
      · iunfold net.opErr at H
        icases H with ⟨%pe, %nw, %hpe, -⟩
        ipureintro; exact .inr (.inr ⟨pe, hpe.1⟩)
    · obtain ⟨msg, h, -⟩ := h; ipureintro; exact .inr (.inl ⟨msg, h⟩)
  · ipureintro; exact .inl ⟨x, hx⟩
  · ipureintro; exact .inl ⟨x, hx.1⟩

/-- An `*OpError` that `readRequest` returns is read-only, of net's own errors and addresses
(`net.opErrOk`, what `OpError.Timeout` needs). -/
theorem reqErr_opErr (γe : GName) (pe : Loc) :
    reqErr (crHeadErr (GF := GF) γe) (interface.mkOk (go.GoType.PointerType net.OpError.ty) #pe) ⊢
      ∃ v : net.OpError, pe ↦□ v ∗ net.opErrOk v := by
  have hne : go.GoType.PointerType net.OpError.ty ≠ go.GoType.PointerType errors.errorString.ty := by
    unfold net.OpError.ty errors.errorString.ty; intro h; cases h
  have hne2 : go.GoType.PointerType net.OpError.ty ≠ net.textproto.ProtocolError.ty := by
    unfold net.OpError.ty net.textproto.ProtocolError.ty; intro h; cases h
  iintro #H
  iunfold reqErr at H
  icases H with (H | ⟨%x, %hx, -⟩ | ⟨%x, %s, %hx, -⟩)
  · iunfold mimeErr at H
    icases H with (⟨%r, #H⟩ | %h)
    · iunfold crHeadErr at H
      icases H with ⟨-, -, H⟩
      iunfold crErrId at H
      icases H with (⟨%xe, %hx, -⟩ | ⟨%src, %addr, %e', #Hop, #Hown, #Hs, #Ha⟩)
      · exact absurd ((interface_mkOk_inj _ _ _ _).1 hx).1 hne
      · icases net.opErr_opErrOk _ _ _ _ _ $$ [$Hop $Hown $Hs $Ha] with ⟨%pe', %v, %hpe, #Hpe, #Hok⟩
        obtain ⟨-, hv⟩ := (interface_mkOk_inj _ _ _ _).1 hpe
        rw [go.intoVal_inj hv]
        iexists v; iframe Hpe Hok
    · obtain ⟨msg, h, -⟩ := h
      exact absurd ((interface_mkOk_inj _ _ _ _).1 h).1 hne2
  · exact absurd ((interface_mkOk_inj _ _ _ _).1 hx).1 hne
  · exact absurd ((interface_mkOk_inj _ _ _ _).1 hx.1).1 hne

theorem opError_ty_ne_errorString :
    go.GoType.PointerType net.OpError.ty ≠ go.GoType.PointerType errors.errorString.ty := by
  unfold net.OpError.ty errors.errorString.ty; intro h; cases h

theorem protocolError_ty_ne_errorString :
    net.textproto.ProtocolError.ty ≠ go.GoType.PointerType errors.errorString.ty := by
  unfold net.textproto.ProtocolError.ty errors.errorString.ty; intro h; cases h

/-- Two `*errorString`s whose messages differ are different pointers. -/
theorem errorString_ne (x y : Loc) (s1 s2 : GoString) (h : s1 ≠ s2) :
    (x.[errors.errorString, go!"s"] ↦□ s1 : IProp GF) ∗ y.[errors.errorString, go!"s"] ↦□ s2 ⊢
      ⌜interface.mkOk (go.GoType.PointerType errors.errorString.ty) #x ≠
        interface.mkOk (go.GoType.PointerType errors.errorString.ty) #y⌝ := by
  iintro ⟨#H1, #H2⟩
  by_cases hxy : x = y
  · subst hxy
    icombine H1 H2 gives %h'
    exact absurd h' h
  · ipureintro
    intro he
    exact hxy (go.intoVal_inj ((interface_mkOk_inj _ _ _ _).1 he).2)

/-- `readRequest`'s error is never `errTooLarge`. -/
theorem reqErr_not_tooLarge (γe : GName) (err : GoInterface) :
    httpEnv (GF := GF) ∗ readEnv ∗ reqErr (crHeadErr γe) err ⊢
      ∃ xt : Loc, globalAddr net.http.errTooLarge ↦□
        interface.mkOk (go.GoType.PointerType errors.errorString.ty) #xt ∗
        ⌜err ≠ interface.mkOk (go.GoType.PointerType errors.errorString.ty) #xt⌝ := by
  iintro ⟨#Henv, #Hrenv, #H⟩
  ihave %Hsh := reqErr_shape γe err $$ H
  iunfold httpEnv at Henv
  icases Henv with ⟨-, -, -, -, ⟨-, -, Htl⟩, -⟩
  iunfold errors.newVar at Htl
  icases Htl with ⟨%xt, #Hg, #Hs, -⟩
  iexists xt
  iframe Hg
  rcases Hsh with ⟨x, hx⟩ | ⟨msg, hx⟩ | ⟨pe, hx⟩
  · iunfold reqErr at H
    iunfold readEnv at Hrenv
    icases Hrenv with ⟨Heof, -, Hueof⟩
    iunfold errors.newVar at Heof
    icases Heof with ⟨%x0, #Hg0, #Hs0, -⟩
    iunfold errors.newVar at Hueof
    icases Hueof with ⟨%x1, #Hg1, #Hs1, -⟩
    icases H with (H | ⟨%x', %hx', #He⟩ | ⟨%x', %s, %hx', #He⟩)
    · iunfold mimeErr at H
      icases H with (⟨%r, #H⟩ | %h)
      · iunfold crHeadErr at H
        icases H with ⟨-, -, H⟩
        iunfold crErrId at H
        icases H with (⟨%xe, %hxe, #He⟩ | ⟨%src, %addr, %e', H, -⟩)
        · icombine He Hg0 gives %h0
          rw [h0]
          iapply errorString_ne x0 xt go!"EOF" go!"http: request too large" (by decide)
          iframe Hs0 Hs
        · iunfold net.opErr at H
          icases H with ⟨%pe, %nw, %hpe, -⟩
          rw [hpe.1] at hx
          exact absurd ((interface_mkOk_inj _ _ _ _).1 hx).1
            (by unfold net.OpError.ty errors.errorString.ty; intro h; cases h)
      · obtain ⟨msg, h, -⟩ := h
        rw [h] at hx
        exact absurd ((interface_mkOk_inj _ _ _ _).1 hx).1
          (by unfold net.textproto.ProtocolError.ty errors.errorString.ty; intro h; cases h)
    · icombine He Hg1 gives %h1
      rw [h1]
      iapply errorString_ne x1 xt go!"unexpected EOF" go!"http: request too large" (by decide)
      iframe Hs1 Hs
    · rw [hx'.1]
      iapply errorString_ne x' xt s go!"http: request too large"
      · intro hs; rw [hs] at hx'; exact absurd hx'.2 (by decide)
      iframe He Hs
  · ipureintro; rw [hx]; intro h
    exact absurd ((interface_mkOk_inj _ _ _ _).1 h).1
      (by unfold net.textproto.ProtocolError.ty errors.errorString.ty; intro h; cases h)
  · ipureintro; rw [hx]; intro h
    exact absurd ((interface_mkOk_inj _ _ _ _).1 h).1
      (by unfold net.OpError.ty errors.errorString.ty; intro h; cases h)

/-- `isUnsupportedTEError(err)` on `readRequest`'s error: `false`. -/
theorem wp_isUnsupportedTEError (γe : GName) (err : GoInterface) :
    {{ reqErr (crHeadErr (GF := GF) γe) err }}
      (App (Val (@! net.http.isUnsupportedTEError)) (Val #err))
    {{ RET #false; True }} := by
  wp_start as #H
  ihave %Hsh := reqErr_shape γe err $$ H
  rcases Hsh with ⟨x, hx⟩ | ⟨msg, hx⟩ | ⟨pe, hx⟩ <;> subst hx <;> wp_auto
  all_goals (iapply HΦ; itrivial)

/-- `isCommonNetReadError(err)` on `readRequest`'s error: either answer. -/
theorem wp_isCommonNetReadError (wp_Timeout : net.OpError.Timeout.spec (GF := GF) (hG := hG))
    (γe : GName) (err : GoInterface) :
    {{ reqErr (crHeadErr (GF := GF) γe) err ∗ readEnv }}
      (App (Val (@! net.http.isCommonNetReadError)) (Val #err))
    {{ (b : Bool), RET #b; True }} := by
  wp_start as ⟨#H, #Hrenv⟩
  ihave %Hsh := reqErr_shape γe err $$ H
  iunfold readEnv at Hrenv
  icases Hrenv with ⟨Heof, -, -⟩
  iunfold errors.newVar at Heof
  icases Heof with ⟨%x0, #Hg0, -, -⟩
  rcases Hsh with ⟨x, hx⟩ | ⟨msg, hx⟩ | ⟨pe, hx⟩ <;> subst hx <;> wp_auto
  · wp_if_destruct
    · iapply HΦ; itrivial
    have h1 : go.typeSetContains (go.GoType.PointerType errors.errorString.ty) net.Error.ty = false := by
      go_type_set
    simp only [h1]
    wp_auto
    iapply HΦ; itrivial
  · have h1 : go.typeSetContains net.textproto.ProtocolError.ty net.Error.ty = false := by
      go_type_set
    simp only [h1]
    wp_auto
    iapply HΦ; itrivial
  · ihave ⟨%v, #Hpe, #Hok⟩ := reqErr_opErr γe pe $$ H
    have h1 : go.typeSetContains (go.GoType.PointerType net.OpError.ty) net.Error.ty = true := by
      go_type_set
    simp only [h1]
    wp_auto
    wp_apply wp_Timeout $$ [$Hpe $Hok] as %b -
    ihave #H2 := Hpe
    iStructNamed H2
    cases b
    · wp_auto
      wp_if_destruct
      · iapply HΦ; itrivial
      · iapply HΦ; itrivial
    · wp_auto
      iapply HΦ; itrivial

/-- `s.readHeaderTimeout()` on `http.Serve`'s server: `0`. -/
theorem wp_readHeaderTimeout (s : Loc) :
    {{ srvServe (GF := GF) s ∗ srvDflt s }}
      (App (Val (s @!! go.GoType.PointerType net.http.Server.ty @!! go!"readHeaderTimeout")) (Val #()))
    {{ RET #(W64 0); True }} := by
  wp_start as ⟨#Hss, #Hsd⟩
  iunfold srvServe at Hss
  icases Hss with ⟨#HRHT, -, -, -⟩
  iunfold srvDflt at Hsd
  icases Hsd with ⟨#HRT, -, -, -⟩
  wp_auto
  iapply HΦ; itrivial

/-- `s.protocols()` on `http.Serve`'s server: HTTP/1 and HTTP/2. -/
theorem wp_protocols (s : Loc) :
    {{ srvServe (GF := GF) s }}
      (App (Val (s @!! go.GoType.PointerType net.http.Server.ty @!! go!"protocols")) (Val #()))
    {{ RET #({ bits' := W8 3 } : net.http.Protocols); True }} := by
  wp_start as #Hss
  iunfold srvServe at Hss
  icases Hss with ⟨-, #HP, #HTN, -⟩
  wp_auto
  repeat (first
    | (rw [method_unfold (t := go.GoType.PointerType net.http.Protocols.ty) (m := go!"SetHTTP1")];
        try wp_auto)
    | (rw [method_unfold (t := go.GoType.PointerType net.http.Protocols.ty) (m := go!"SetHTTP2")];
        try wp_auto)
    | (rw [method_unfold (t := go.GoType.PointerType net.http.Protocols.ty) (m := go!"setBit")];
        try wp_auto)
    | wp_if_destruct | wp_auto)
  all_goals (rw [show ((0 : w8) ||| W8 1 ||| W8 2) = W8 3 by decide]; iapply HΦ; itrivial)
  all_goals sorry

/-- `s.shuttingDown()` on `http.Serve`'s server: `false`. -/
theorem wp_shuttingDown (s : Loc) :
    {{ srvServe (GF := GF) s ∗ isPkgInit (PROP := IProp GF) pkg_id.sync.atomic }}
      (App (Val (s @!! go.GoType.PointerType net.http.Server.ty @!! go!"shuttingDown")) (Val #()))
    {{ RET #false; True }} := by
  wp_start as ⟨#Hss, #Hat⟩
  iunfold srvServe at Hss
  icases Hss with ⟨-, -, -, #Hsd⟩
  wp_auto
  wp_bind (App (Val #(methods _ _ _)) (Val #()))
  iapply (sync.atomic.Bool.wp_Load
    (structFieldRef net.http.Server go!"inShutdown" s) DFrac.discard)
  · iexact Hat
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iexists false
  iframe Hsd
  iintro -
  imod Hmask
  imodintro
  wp_auto
  iapply HΦ; itrivial

/-- `bw.Flush()` of a writer holding nothing: no write, the writer unchanged. -/
theorem wp_rawFlush [bufio.Assumptions] (bw : Loc) (sz : Nat) :
    {{ EtcdGrove.bufio.rawWriter (GF := GF) bw sz }}
      (App (Val (bw @!! go.GoType.PointerType bufio.Writer.ty @!! go!"Flush")) (Val #()))
    {{ (e : GoInterface), RET #e; EtcdGrove.bufio.rawWriter bw sz }} := by
  wp_start as Hraw
  iunfold EtcdGrove.bufio.rawWriter at Hraw
  icases Hraw with ⟨%v, %bs, Hb, Hbuf, %Hv⟩
  have hn := Hv.2.2
  wp_auto
  rcases hE : v.err' with _ | i
  all_goals wp_auto
  all_goals try (simp only [hn, decide_true]; wp_auto)
  all_goals
    iapply HΦ
    iunfold EtcdGrove.bufio.rawWriter
    iexists v, bs
    iframe Hb Hbuf
    ipureintro; exact Hv

/-- `putBufioReader(br)` of a raw reader: reset to `nil`, back in `bufioReaderPool`. -/
theorem wp_putBufioReader [bufio.Assumptions]
    (wp_Reset : EtcdGrove.bufio.Reader.Reset.spec (GF := GF) (hG := hG)) (br : Loc) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync ∗ rPool ∗ EtcdGrove.bufio.rawReader (GF := GF) br }}
      (App (Val (@! net.http.putBufioReader)) (Val #br))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hpool, Hraw⟩
  wp_auto
  wp_apply wp_Reset br _ $$ [$Hraw] as Hfr
  · ipureintro; left; rfl
  ihave Hraw := EtcdGrove.bufio.freshReader_raw _ _ $$ Hfr
  try wp_auto
  iunfold rPool at Hpool
  wp_apply sync.Pool.wp_Put $$ [$Hpool Hraw]
  · iunfold rPoolP; iexists br; iframe Hraw; ipureintro; rfl
  iapply HΦ; itrivial

/-- `c.close()` of a connection whose buffered reader and writer are raw (nothing read past what
was consumed, nothing written through the writer): both back in their pools, the connection
closed. -/
theorem wp_conn_close [bufio.Assumptions]
    (wp_Close : net.Conn.Close.spec (GF := GF) (hG := hG))
    (wp_RReset : EtcdGrove.bufio.Reader.Reset.spec (GF := GF) (hG := hG))
    (wp_WReset : EtcdGrove.bufio.Writer.Reset.spec (GF := GF) (hG := hG))
    (c br bw t : Loc) (cn : Nat) (a : GoString) (la ra : GoInterface) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync ∗ rPool ∗ wPools ∗
        structFieldRef net.http.conn go!"bufr" c ↦ br ∗ EtcdGrove.bufio.rawReader br ∗
        structFieldRef net.http.conn go!"bufw" c ↦ bw ∗ EtcdGrove.bufio.rawWriter bw 4096 ∗
        structFieldRef net.http.conn go!"rwc" c ↦□
          interface.mkOk (go.GoType.PointerType net.TCPConn.ty) #t ∗
        connAt t cn true a la ra ∗ connIs (Gg := hG.goose_globalGS) cn }}
      (App (Val (c @!! go.GoType.PointerType net.http.conn.ty @!! go!"close")) (Val #()))
    {{ RET #(); structFieldRef net.http.conn go!"bufr" c ↦ (null : Loc) ∗
        structFieldRef net.http.conn go!"bufw" c ↦ (null : Loc) }} := by
  wp_start as ⟨#Hrpool, #Hwpools, Hbr, Hraw, Hbw, Hwraw, #Hrwc, #Hca, #Hci⟩
  wp_auto
  rw [method_unfold (t := go.GoType.PointerType net.http.conn.ty) (m := go!"finalFlush")]
  iunfold EtcdGrove.bufio.rawReader at Hraw
  icases Hraw with ⟨%rv, %rbs, Hrb, Hrbuf, %Hrv⟩
  icases typedPointsto_not_null_dup _ _ _ $$ Hrb with ⟨Hrb, %Hbrnn⟩
  ihave Hraw : EtcdGrove.bufio.rawReader br $$ [Hrb Hrbuf]
  · iunfold EtcdGrove.bufio.rawReader; iexists rv, rbs; iframe Hrb Hrbuf; ipureintro; exact Hrv
  iunfold EtcdGrove.bufio.rawWriter at Hwraw
  icases Hwraw with ⟨%wv, %wbs, Hwb, Hwbuf, %Hwv⟩
  icases typedPointsto_not_null_dup _ _ _ $$ Hwb with ⟨Hwb, %Hbwnn⟩
  ihave Hwraw : EtcdGrove.bufio.rawWriter bw 4096 $$ [Hwb Hwbuf]
  · iunfold EtcdGrove.bufio.rawWriter; iexists wv, wbs; iframe Hwb Hwbuf; ipureintro; exact Hwv
  wp_auto
  simp only [Hbrnn, decide_false, Bool.not_false]
  wp_auto
  wp_apply wp_putBufioReader wp_RReset br $$ [$Hrpool $Hraw]
  try wp_auto
  simp only [Hbwnn, decide_false, Bool.not_false]
  try wp_auto
  wp_apply wp_rawFlush bw 4096 $$ [$Hwraw] as %e Hwraw
  try wp_auto
  wp_apply wp_putBufioWriter wp_WReset bw 4096 (.inr rfl) $$ [$Hwpools $Hwraw]
  try wp_auto
  wp_apply wp_Close t cn true a la ra (fun _ => iprop(True)) $$ [$Hca] as %err -
  · imod close_au (Gg := hG.goose_globalGS) cn true $$ Hci with ⟨%st, %d, Hst, Hd, Hk⟩
    imodintro
    iexists st, d
    iframe Hst Hd
    iintro %res %st' %d' %Hco Hst' Hd'
    imod Hk $$ %res %st' %d' %Hco Hst' Hd' with -
    imodintro
    itrivial
  try wp_auto
  iapply HΦ
  iframe

/-- `fmt.Fprintf(w, f)` of a format `f` without a verb and no arguments: one `w.Write` of `f`'s bytes.
(Perennial's `fmt.Fprintf.spec` lets the writer's spec see any bytes (`fmt.writeSpec`), not which;
this is its proof (`Perennial/Proof/fmt/Fprintf.lean`, over the Go model's printer) where the bytes
written are `SprintfOut`'s output, here `f`: over the same callees.) -/
theorem wp_Fprintf_noVerb [fmt.Assumptions]
    (wp_newPrinter : fmt.newPrinter.spec (GF := GF) (hG := hG))
    (wp_writeString : fmt.buffer.writeString.spec (GF := GF) (hG := hG))
    (wp_free : fmt.pp.free.spec (GF := GF) (hG := hG))
    (wp_Choose : internal.gomodel.Choose.spec (GF := GF) (hG := hG))
    (wp_ChooseUint64 : internal.gomodel.ChooseUint64.spec (GF := GF) (hG := hG))
    (ii : GoInterfaceOk) (f : GoString)
    (hf : f.all (fun c => decide (c ≠ W8 37)) = true) (P : IProp GF) (Q : w64 → GoInterface → IProp GF) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.fmt ∗ P ∗
        (∀ (sl : GoSlice) (Φ : val → IProp GF), P -∗ sl ↦* f -∗
          ▷ (∀ (n : w64) (err : GoInterface), sl ↦* f -∗ Q n err -∗ Φ (PairV #n #err)) -∗
          WP (App (Val #(methods ii.ty go!"Write" ii.v)) (Val #sl)) {{ Φ }}) }}
      (App (App (App (Val (@! fmt.Fprintf)) (Val #(interface.ok ii))) (Val #f)) (Val #slice.nil))
    {{ (n : w64) (err : GoInterface), RET (PairV #n #err); Q n err }} := by
  wp_start as ⟨HP, HW⟩
  try wp_auto
  wp_apply wp_newPrinter as %p Hp
  unfold fmt.isPrinterAny fmt.isPrinter fmt.isPrinterA
  icases Hp with ⟨%hnn, %F, %wid, %prec, %x', Hb, Hrest⟩
  ihave Hsl := ownSlice_nil (V := GoInterface) (DFrac.own 1)
  have hdo := fmt.wp_doPrintf wp_Choose wp_ChooseUint64 wp_writeString (p.[fmt.pp, go!"buf"]) []
    f slice.nil [] (DFrac.own 1) false
  rw [fmt.modeVerbs_false] at hdo
  wp_apply hdo $$ [$Hb $Hsl] as %wsl %unk ⟨%s, Hb, -, %Hs, -⟩
  · iapply fmt.argsOk_of_argsWf; exact fmt.ArgsWf.nil
  have hs := SprintfOut_noVerb (fun c hc => by
    have := List.all_eq_true.1 hf c hc; simpa using this) Hs
  subst hs
  try wp_auto
  unfold fmt.bufferOwn
  icases Hb with ⟨%sl, Hb, Hbs, Hcap⟩
  wp_auto
  wp_bind (App (Val #(methods ii.ty go!"Write" ii.v)) (Val #sl))
  iapply HW $$ HP Hbs
  inext
  iintro %n %err Hbs HQ
  wp_auto
  wp_apply wp_free p ([] ++ s) $$ [Hb Hbs Hcap Hrest]
  · iframe
    unfold fmt.isPrinterAny fmt.isPrinter fmt.isPrinterA fmt.bufferOwn
    isplitr
    · ipureintro; exact hnn
    iexists F, wid, prec, x'
    iframe
  try wp_auto
  iapply HΦ
  iexact HQ

end lemmas

end net.http
end Perennial

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
      icases H with (⟨%xe, %hx, -⟩ | ⟨%src, %addr, %e', H⟩)
      · ipureintro; exact .inl ⟨xe, hx⟩
      · iunfold net.opErr at H
        icases H with ⟨%pe, %nw, %hpe, -⟩
        ipureintro; exact .inr (.inr ⟨pe, hpe.1⟩)
    · obtain ⟨msg, h, -⟩ := h; ipureintro; exact .inr (.inl ⟨msg, h⟩)
  · ipureintro; exact .inl ⟨x, hx⟩
  · ipureintro; exact .inl ⟨x, hx.1⟩

/-- An `*OpError` that `readRequest` returns is read-only. -/
theorem reqErr_opErr (γe : GName) (pe : Loc) :
    reqErr (crHeadErr (GF := GF) γe) (interface.mkOk (go.GoType.PointerType net.OpError.ty) #pe) ⊢
      ∃ v : net.OpError, pe ↦□ v := by
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
      icases H with (⟨%xe, %hx, -⟩ | ⟨%src, %addr, %e', H⟩)
      · exact absurd ((interface_mkOk_inj _ _ _ _).1 hx).1 hne
      · iunfold net.opErr at H
        icases H with ⟨%pe', %nw, %hpe, #Hpe⟩
        obtain ⟨-, hv⟩ := (interface_mkOk_inj _ _ _ _).1 hpe.1
        rw [go.intoVal_inj hv]
        iexists _; iexact Hpe
    · obtain ⟨msg, h, -⟩ := h
      exact absurd ((interface_mkOk_inj _ _ _ _).1 h).1 hne2
  · exact absurd ((interface_mkOk_inj _ _ _ _).1 hx).1 hne
  · exact absurd ((interface_mkOk_inj _ _ _ _).1 hx.1).1 hne

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
      ∃ v : GoInterface, globalAddr net.http.errTooLarge ↦□ v ∗ ⌜err ≠ v⌝ := by
  iintro ⟨#Henv, #Hrenv, #H⟩
  ihave %Hsh := reqErr_shape γe err $$ H
  iunfold httpEnv at Henv
  icases Henv with ⟨-, -, -, -, ⟨-, -, Htl⟩, -⟩
  iunfold errors.newVar at Htl
  icases Htl with ⟨%xt, #Hg, #Hs, -⟩
  iexists _
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
        icases H with (⟨%xe, %hxe, #He⟩ | ⟨%src, %addr, %e', H⟩)
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
  · ihave ⟨%v, #Hpe⟩ := reqErr_opErr γe pe $$ H
    have h1 : go.typeSetContains (go.GoType.PointerType net.OpError.ty) net.Error.ty = true := by
      go_type_set
    simp only [h1]
    wp_auto
    wp_apply wp_Timeout $$ [$Hpe] as %b -
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

end lemmas

end net.http
end Perennial

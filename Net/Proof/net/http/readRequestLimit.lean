/-
The proof of `readRequestLimit` on net/rpc's `CONNECT` request (`Net/Spec/net/http/readRequestLimit.lean`).

The request line is read whole (`modelReadLine`: the stream's bytes are a prefix of
`connectReq path = reqLine path ++ "\n\n"`, so the line is `reqLine path`) or cut by an error, after
which the stream stays where it is: either way the line is a prefix of `reqLine path`, whose parse
(`parseRequestLine`, the two `modelCutByte`s: `cutByte_prefix`) finds `CONNECT`, the path and a prefix
of `"HTTP/1.0"` (`parse_prefix`), which `ParseHTTPVersion` accepts only whole. Then the URL
(`modelParseRequestURI` on the `reqPath`), the empty header block (`modelReadMIMEHeader` over `[]`: read
whole only after a whole line), `fixPragmaCacheControl`, `shouldClose`, `readTransfer` on the request
(no body) and `isH2Upgrade` (not `PRI`). Every error goes through the deferred rewrite of `io.EOF`,
which compares it with `io.EOF`: a pointer's value is a location (`io.ptrTyped`).
-/
module

public import Net.Spec.net.http.readRequestLimit
public import Net.Spec.net.http.modelReadLine
public import Net.Spec.net.http.modelReadMIMEHeader
public import Net.Spec.net.http.parseRequestLine
public import Net.Spec.net.http.validMethod
public import Net.Spec.net.http.ParseHTTPVersion
public import Net.Spec.net.http.badStringError
public import Net.Spec.net.http.modelParseRequestURI
public import Net.Spec.net.http.fixPragmaCacheControl
public import Net.Spec.net.http.shouldClose
public import Net.Spec.net.http.readTransfer
public import Net.Proof.net.http.HdrLemmas
public import Perennial.Spec.strings.HasPrefix

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace net.http

section pure

/-- The request line of net/rpc's `CONNECT` request. -/
def reqLine (path : List w8) : List w8 := go!"CONNECT " ++ path ++ go!" HTTP/1.0"

theorem connectReq_split (path : List w8) :
    net.rpc.connectReq path = reqLine path ++ W8 10 :: [W8 10] := by
  simp [net.rpc.connectReq, reqLine]

theorem reqPath_no (path : List w8) (hp : reqPath path) (c : w8) (hc : pathByte c = false) :
    c ∉ path := fun h => by rw [hp.2 c h] at hc; cases hc

theorem reqLine_no_nl (path : List w8) (hp : reqPath path) : W8 10 ∉ reqLine path := by
  have := reqPath_no path hp (W8 10) (by decide)
  intro hm
  simp only [reqLine, List.mem_append] at hm
  rcases hm with (hm | hm) | hm
  · exact absurd hm (by decide)
  · exact this hm
  · exact absurd hm (by decide)

theorem dropCR_reqLine (path : List w8) : dropCR (reqLine path) = reqLine path := by
  unfold dropCR reqLine
  rw [List.getLast?_append]
  simp

/-- `cutByte` of a prefix of `a ++ c :: b`, `a` without `c`: no `c` read yet (the prefix is within
`a`), or the cut at `a`'s end, the rest a prefix of `b`. -/
theorem cutByte_prefix {c : w8} : ∀ {a b l : List w8}, c ∉ a → l <+: a ++ c :: b →
    (cutByte l c = (l, [], false) ∧ l <+: a) ∨ (∃ l', cutByte l c = (a, l', true) ∧ l' <+: b)
  | [], b, l, _, h => by
    cases l with
    | nil => left; exact ⟨rfl, List.nil_prefix⟩
    | cons x l =>
      obtain ⟨t, ht⟩ := h
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at ht
      obtain ⟨rfl, ht⟩ := ht
      right
      refine ⟨l, ?_, ⟨t, ht⟩⟩
      simp [cutByte, List.findIdx?_cons]
  | y :: a, b, l, ha, h => by
    cases l with
    | nil => left; exact ⟨rfl, List.nil_prefix⟩
    | cons x l =>
      obtain ⟨t, ht⟩ := h
      simp only [List.cons_append, List.cons.injEq] at ht
      obtain ⟨rfl, ht⟩ := ht
      have hy : x ≠ c := fun h => ha (h ▸ List.mem_cons_self)
      have ha' : c ∉ a := fun h => ha (List.mem_cons_of_mem _ h)
      have hc : cutByte (x :: l) c =
          match cutByte l c with
          | (p, q, f) => (if f then (x :: p, q, f) else (x :: p, q, f)) := by
        unfold cutByte
        rw [List.findIdx?_cons]
        simp only [decide_eq_true_eq, hy, ↓reduceIte]
        cases h : List.findIdx? (fun z => decide (z = c)) l with
        | none => simp
        | some i => simp [List.take_succ_cons, List.drop_succ_cons]
      rcases cutByte_prefix (b := b) (l := l) ha' ⟨t, ht⟩ with ⟨h1, h2⟩ | ⟨l', h1, h2⟩
      · left
        rw [hc, h1]
        exact ⟨by simp, (List.prefix_cons_inj _).2 h2⟩
      · right
        refine ⟨l', ?_, h2⟩
        rw [hc, h1]
        simp

/-- The parse of a prefix of the request line: when it finds both spaces, the method `CONNECT`, the
path, and a prefix of the version. -/
theorem parse_prefix {path line : List w8} (hp : reqPath path) (h : line <+: reqLine path)
    (hok : (parseReqLine line).2.2.2 = true) :
    (parseReqLine line).1 = go!"CONNECT" ∧ (parseReqLine line).2.1 = path ∧
      (parseReqLine line).2.2.1 <+: go!"HTTP/1.0" := by
  have hs : W8 32 ∉ go!"CONNECT" := by decide
  have h1 : line <+: go!"CONNECT" ++ W8 32 :: (path ++ W8 32 :: go!"HTTP/1.0") := by
    simpa [reqLine] using h
  unfold parseReqLine at hok ⊢
  rcases cutByte_prefix hs h1 with ⟨e1, -⟩ | ⟨l1, e1, p1⟩
  · simp only [e1] at hok; simp at hok
  have hsp : W8 32 ∉ path := reqPath_no path hp (W8 32) (by decide)
  rcases cutByte_prefix hsp p1 with ⟨e2, -⟩ | ⟨l2, e2, p2⟩
  · simp only [e1, e2] at hok; simp at hok
  simp only [e1, e2, Bool.and_self, ↓reduceIte]
  exact ⟨trivial, trivial, p2⟩

end pure

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : net.http.Assumptions]

/-- A `textproto.ProtocolError`'s `Error()` returns its message. -/
theorem protocolError_msg (msg : GoString) :
    ⊢ (□ ∀ Φ : val → IProp GF, ▷ Φ #msg -∗
      WP (App (Val #(methods net.textproto.ProtocolError.ty go!"Error" #msg)) (Val #())) {{ Φ }}) := by
  iintro !>
  iintro %Φ HΦ
  rw [method_unfold (t := net.textproto.ProtocolError.ty) (m := go!"Error")]
  wp_auto
  iapply HΦ

/-- The header reader's errors have an `Error()` method. -/
theorem mimeErr_msg (E : List w8 → GoInterface → IProp GF) (err : GoInterface) :
    (□ ∀ (r : List w8) (e : GoInterface), E r e -∗ errMsgOk e) ∗ mimeErr E err ⊢ errMsgOk err := by
  iintro ⟨#Herrs, #Hm⟩
  iunfold mimeErr at Hm
  icases Hm with (⟨%r, #HE⟩ | %Hp)
  · iapply Herrs $$ HE
  · obtain ⟨msg, rfl, hp⟩ := Hp
    iapply errMsgOk_of ⟨net.textproto.ProtocolError.ty, #msg⟩ msg
      (fun h => by subst h; exact absurd hp (by decide))
    iapply protocolError_msg

/-- `r.isH2Upgrade()` on a request whose method is not `PRI`: `false`. -/
theorem wp_isH2Upgrade (r : Loc) (rq : net.http.Request) (h : rq.Method' ≠ go!"PRI") :
    {{ (r ↦ rq : IProp GF) }}
      (App (Val #(methods (go.GoType.PointerType net.http.Request.ty) go!"isH2Upgrade" #r)) (Val #()))
    {{ RET #false; r ↦ rq }} := by
  wp_start as Hr
  wp_auto
  rw [decide_eq_false h]
  wp_auto
  iapply HΦ; iexact Hr

set_option hygiene false in
/-- An error return (`e`, a pointer when of a pointer type: `Hpe`; one of `reqErr`'s: `Hre`), through
the deferred rewrite of `io.EOF` (`xe`, `xu`: `io.EOF`'s and `io.ErrUnexpectedEOF`'s locations). -/
local macro "rrl_fail" : tactic => `(tactic| (
  try wp_auto
  by_cases hty : e.ty = go.GoType.PointerType errors.errorString.ty
  · obtain ⟨l0, hl0⟩ := Hpe e _ rfl hty
    obtain ⟨ty, v⟩ := e
    simp only at hty hl0
    subst hty hl0
    simp only [↓reduceIte]
    wp_auto
    wp_if_destruct
    all_goals (try wp_auto); iapply HΦ; ileft; isplitr; (· ipureintro; simp [interface.mkOk])
    all_goals first
      | iexact Hre
      | (iunfold reqErr; iright; ileft; iexists xu; iframe Hxu; ipureintro; rfl)
  · simp only [hty, ↓reduceIte]
    try wp_auto
    iapply HΦ
    ileft; isplitr
    · ipureintro; simp
    iexact Hre))

theorem readRequestLimit.wp_proof
    (wp_ReadLine : modelReadLine.spec (GF := GF) (hG := hG))
    (wp_MIME : modelReadMIMEHeader.spec (GF := GF) (hG := hG))
    (wp_parse : parseRequestLine.spec (GF := GF) (hG := hG))
    (wp_valid : validMethod.spec (GF := GF) (hG := hG))
    (wp_Version : ParseHTTPVersion.spec (GF := GF) (hG := hG))
    (wp_bad : badStringError.spec (GF := GF) (hG := hG))
    (wp_URI : modelParseRequestURI.spec (GF := GF) (hG := hG))
    (wp_pragma : fixPragmaCacheControl.spec (GF := GF) (hG := hG))
    (wp_shouldClose : shouldClose.spec (GF := GF) (hG := hG))
    (wp_transfer : readTransfer.spec (GF := GF) (hG := hG))
    (wp_HasPrefix : strings.HasPrefix.spec (GF := GF) (hG := hG)) :
    readRequestLimit.spec (GF := GF) (hG := hG) := by
  intro b ri S E path maxH hp hmax
  iintro #Henv #Hstream #Hbound #Hlaw1 #Hlaw2 #Herrs
  wp_start as Hb
  wp_auto
  wp_apply wp_with_defer as %defer Hdefer
  wp_apply wp_ReadLine b ri S E [] $$ Hstream Hbound [Hb] as %line %err ⟨%l, %Hl10, Hcase⟩
  · iexact Hb
  -- the line read: the whole request line, a prefix of it (cut by an error), or an error
  ihave Hu : ((⌜line = [] ∧ err ≠ GoInterface.nil⌝ ∗ ∃ r0 : List w8, □ E r0 err) ∨
      (⌜err = GoInterface.nil ∧ line <+: reqLine path⌝ ∗
        ∃ rr : List w8, EtcdGrove.bufio.ownReader b ri S E rr ∗
        (⌜rr = reqLine path ++ [W8 10] ∧ line = reqLine path⌝ ∨
          (⌜rr = line⌝ ∗ □ ∀ r', S r' -∗ ⌜rr <+: r' → r' = rr⌝))) : IProp GF)
      $$ [Hcase]
  · icases Hcase with (⟨⟨%Herr, %Hline⟩, Hb⟩ | ⟨%e, %He, #Hea, Hb, %Hcases⟩)
    · ihave ⟨%q, HS, Hcl⟩ := EtcdGrove.bufio.ownReader_open b ri S E _ $$ Hb
      ihave %Hp := Hlaw1 $$ HS
      ihave Hb := Hcl $$ HS
      simp only [List.nil_append] at Hp
      have hl : l = reqLine path := by
        refine prefix_nl Hl10 (reqLine_no_nl path hp) (t := [W8 10]) ?_
        rw [← connectReq_split]
        exact (List.prefix_append _ _).trans Hp
      subst hl
      have hline : line = reqLine path := by rw [Hline, dropCR_reqLine]
      iright
      isplitr
      · ipureintro; exact ⟨Herr, hline ▸ List.prefix_refl _⟩
      iexists [] ++ reqLine path ++ [W8 10]
      iframe Hb
      ileft
      ipureintro; exact ⟨by simp, hline⟩
    · rcases Hcases with ⟨hne, hnil, hline⟩ | ⟨hnil, herr, hline⟩
      · unfold EtcdGrove.io.errAt
        icases Hea with ⟨(%Hen | #HE), %Hty⟩
        · exact absurd Hen He
        ihave ⟨%q, HS, Hcl⟩ := EtcdGrove.bufio.ownReader_open b ri S E _ $$ Hb
        ihave %Hp := Hlaw1 $$ HS
        ihave Hb := Hcl $$ HS
        simp only [List.nil_append] at Hp
        have hls : l <+: reqLine path := by
          rw [connectReq_split] at Hp
          exact prefix_no_nl Hl10 (reqLine_no_nl path hp) ((List.prefix_append _ _).trans Hp)
        iright
        isplitr
        · ipureintro; exact ⟨hnil, hline ▸ hls⟩
        iexists [] ++ l
        iframe Hb
        iright
        isplitr
        · ipureintro; simp [hline]
        imodintro
        iintro %r' HS
        iapply Hlaw2 $$ %([] ++ l) %r' %e HE HS
      · ileft
        isplitr
        · ipureintro
          exact ⟨hline, herr ▸ He⟩
        unfold EtcdGrove.io.errAt
        icases Hea with ⟨(%Hen | #HE), -⟩
        · exact absurd Hen He
        subst herr
        iexists _
        iexact HE
  icases Hu with (⟨%Hc, %r0, #HE0⟩ | ⟨⟨%Herr, %Hline⟩, %rr, Hb, Hk⟩)
  · -- nothing read: the error, before the deferred rewrite
    obtain ⟨-, Hne⟩ := Hc
    cases err with
    | nil => exact absurd rfl Hne
    | ok ei =>
    simp only []
    wp_auto
    iapply HΦ
    ileft; isplitr
    · ipureintro; simp
    iunfold reqErr; ileft; iunfold mimeErr; ileft; iexists r0; iexact HE0
  subst Herr
  ihave #Henv' := Henv
  iunfold httpEnv at Henv'
  icases Henv' with ⟨#Hbufio, #Hio, #Hfmt, #Hstrconv, ⟨#Htok, #Hstrs, %ltl, #Htl⟩, %nb, #Hnb⟩
  ihave #Hinit := _root_.Perennial.io.isInit_access $$ Hio
  icases Hinit with ⟨-, -, -, -, #HEOF, #HUEOF, -⟩
  unfold errors.newVar
  icases HEOF with ⟨%xe, #Hxe, -⟩
  icases HUEOF with ⟨%xu, #Hxu, -⟩
  simp only []
  wp_auto
  wp_apply wp_parse line
  generalize hpl : parseReqLine line = pl
  obtain ⟨meth, uri, proto, pok⟩ := pl
  simp only []
  cases pok
  · simp only [Bool.not_false]
    wp_auto
    wp_apply wp_bad $$ Hfmt as %e ⟨%Hpe, %x, %s, %hxs, #Hxs⟩
    ihave #Hre : (reqErr E (interface.ok e) : IProp GF) $$ []
    · iunfold reqErr; iright; iright; iexists x, s; iframe Hxs; ipureintro
      exact ⟨by rw [hxs.1],
        (by decide : (go!"malformed HTTP " : List w8) <+: go!"malformed HTTP request").trans hxs.2⟩
    rrl_fail
  obtain ⟨hm, hu, hpr⟩ := parse_prefix hp Hline (by rw [hpl])
  rw [hpl] at hm hu hpr
  simp only at hm hu hpr
  subst hm hu
  simp only [Bool.not_true]
  wp_auto
  wp_apply wp_valid $$ Htok
  rw [show (!(go!"CONNECT" : List w8).isEmpty && (go!"CONNECT" : List w8).all fieldByte) = true by decide]
  wp_auto
  wp_apply wp_Version proto as %vmaj %vmin %vok %Hvok
  · iframe Henv; ipureintro; exact Or.inl hpr
  obtain ⟨Hvok1, Hvok2⟩ := Hvok
  cases vok
  · simp only [Bool.not_false]
    wp_auto
    wp_apply wp_bad $$ Hfmt as %e ⟨%Hpe, %x, %s, %hxs, #Hxs⟩
    ihave #Hre : (reqErr E (interface.ok e) : IProp GF) $$ []
    · iunfold reqErr; iright; iright; iexists x, s; iframe Hxs; ipureintro
      exact ⟨by rw [hxs.1],
        (by decide : (go!"malformed HTTP " : List w8) <+: go!"malformed HTTP version").trans hxs.2⟩
    rrl_fail
  have hproto : proto = go!"HTTP/1.0" := by
    have h := Hvok1.symm
    simp only [decide_eq_true_eq] at h
    rcases h with h | h
    · exact h
    · exfalso; rw [h] at hpr; exact absurd hpr (by decide)
  subst hproto
  obtain ⟨rfl, rfl⟩ := Hvok2 rfl
  simp only [Bool.not_true]
  wp_auto
  wp_apply wp_HasPrefix $$ Hstrs
  have hslash : decide ((go!"/" : List w8) <+: uri) = true := by
    obtain ⟨h1, -⟩ := hp
    cases uri with
    | nil => cases h1
    | cons x t =>
      simp only [List.head?_cons, Option.some.injEq] at h1
      subst h1
      exact decide_eq_true (List.cons_prefix_cons.2 ⟨rfl, List.nil_prefix⟩)
  rw [hslash]
  simp only [Bool.not_true]
  wp_auto
  wp_apply wp_URI uri as %u Hu
  · ipureintro; exact hp
  -- the header block: empty, read whole only after a whole request line
  ihave ⟨#HL, #Hend⟩ : ((□ ∀ r', S r' -∗ ⌜rr <+: r' → r' <+: rr ++ hdrWire [] [] ++ []⌝) ∗
      (□ ∀ r', S r' -∗ ⌜rr ++ hdrWire [] [] <+: r' → rr = reqLine uri ++ [W8 10]⌝) : IProp GF) $$ [Hk]
  · icases Hk with (⟨%Hrr, -⟩ | ⟨%Hrr, #Hcut⟩)
    · subst Hrr
      isplitl
      · imodintro
        iintro %r' HS
        ihave %h := Hlaw1 $$ HS
        ipureintro
        intro _
        simpa [hdrWire, connectReq_split] using h
      · imodintro
        iintro %r' -
        ipureintro
        intro _; rfl
    · isplitl
      · imodintro
        iintro %r' HS
        ihave %h := Hcut $$ HS
        ipureintro
        intro h1
        rw [h h1, List.append_assoc]
        exact List.prefix_append _ _
      · imodintro
        iintro %r' HS
        ihave %h := Hcut $$ HS
        ipureintro
        intro h1
        exfalso
        have h2 := h ((List.prefix_append _ _).trans h1)
        rw [h2] at h1
        have := h1.length_le
        simp [hdrWire] at this
        omega
  wp_apply wp_MIME b ri S E rr [] [] [] maxH (by decide) (Or.inl rfl) (by simpa using hmax)
      $$ Henv Hstream Hbound HL Hlaw2 [Hb] as %m %merr Hm
  · iexact Hb
  icases Hm with (⟨⟨%Hme, %Hpe⟩, #Hme2⟩ | ⟨%Hmn, Hm, Hb⟩)
  · -- an error: never `"message too large"` (`errMsgOk`), so not `errTooLarge`
    ihave #Hmsg := mimeErr_msg E merr $$ [$Herrs $Hme2]
    iunfold errMsgOk at Hmsg
    icases Hmsg with ⟨%ei, %Hei, #HW⟩
    subst Hei
    ihave #Hre : (reqErr E (interface.ok ei) : IProp GF) $$ []
    · iunfold reqErr; ileft; iexact Hme2
    wp_auto
    wp_bind (App (Val #(methods _ go!"Error" _)) (Val #()))
    iapply HW
    inext
    iintro %msg %Hmsg
    wp_auto
    wp_if_destruct
    · exact absurd rfl Hmsg
    · generalize ei = e at Hpe ⊢
      rrl_fail
  subst Hmn
  ihave ⟨%ms, Hm, Hcv, %Habs⟩ := hdrOwn_open m [] $$ Hm
  have hms : ms = ∅ := GMap.ext fun k => by rw [Habs k (by simp)]; rfl
  subst hms
  wp_auto
  wp_apply (wp_map_lookup1 (V := GoSlice) go.string (go.SliceType go.string) m _ go!"Host" _) $$ Hm
    as Hm
  rw [method_unfold (t := go.GoType.PointerType Header.ty) (m := go!"get")]
  wp_auto
  rw [method_unfold (t := Header.ty) (m := go!"get")]
  wp_auto
  wp_apply (wp_map_lookup1 (V := GoSlice) go.string (go.SliceType go.string) m _ go!"Host" _) $$ Hm
    as Hm
  wp_apply wp_pragma m ∅ $$ [Hm] as Hm
  · iframe Hm; ipureintro; rfl
  wp_apply wp_shouldClose (W64 1) (W64 0) m ∅ false $$ [Hm] as %cl ⟨%ms', Hm, -, %Hms'⟩
  · iframe Hm; iapply hdrVals_none; rfl
  have : ms' = ∅ := by rcases Hms' with h | ⟨h, -⟩; exact h; cases h
  subst this
  wp_apply wp_transfer.2 «$r0_ptr» _ ∅ b maxH $$ [«$r0» Hm] as ⟨%nb', %rqv', Hr0, %Hrqv, Hm⟩
  · isplitr
    · iexact Henv
    isplitl [«$r0»]
    · iexact «$r0»
    simp only []
    isplitl [Hm]
    · iexact Hm
    ipureintro; exact ⟨rfl, rfl, rfl⟩
  have hMeth : rqv'.Method' = go!"CONNECT" := by rw [Hrqv]; simp only [reqNoBody]
  wp_apply wp_isH2Upgrade «$r0_ptr» rqv' (by rw [hMeth]; decide) $$ Hr0 as Hr0
  iapply HΦ
  iright
  isplitr
  · ipureintro; rfl
  ihave ⟨%q, HS, Hcl⟩ := EtcdGrove.bufio.ownReader_open b ri S E _ $$ Hb
  ihave %h := Hend $$ HS
  ihave Hb := Hcl $$ HS
  have hrr := h (List.prefix_append _ _)
  subst hrr
  have heq : rqv' = connectReqVal uri u m cl nb' := by
    rw [Hrqv]; simp only [reqNoBody, connectReqVal, ↓reduceIte]
  rw [heq]
  iunfold connectReqv
  isplitl [Hr0 Hu Hm]
  · iexists u, m, cl, nb'
    iframe Hr0 Hu Hm
  rw [show rpc.connectReq uri = reqLine uri ++ [W8 10] ++ hdrWire [] [] by
    rw [connectReq_split]; simp [hdrWire]]
  iexact Hb

end proof

end net.http
end Perennial

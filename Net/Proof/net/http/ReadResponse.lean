/-
`http.ReadResponse` on net/rpc's `CONNECT` answer or net/http's `400` answer (see
`Net/Spec/net/http/ReadResponse.lean`).

The status line is read whole (`modelReadLine`, then the answer's bytes are a prefix of
`connectAns` or of `badReqAns`, so the line is `statusLine` or `badStatusLine` with its `"\r"`) or cut
by an error, after which the stream stays where it is (the finality law): either way the line is a
prefix of one of the two, and the parse of it either fails (`badStringError`, `Atoi`'s error) or
finds the version `"HTTP/1.0"` or `"HTTP/1.1"` (`proto_of_prefix2`). The header block is read over a
law that the bytes past the reader are a prefix of the block's (`modelReadMIMEHeader`): the empty one
after net/rpc's status line or a cut line, net/http's `400` answer's two lines (`badHdr`) after its
status line; it is read whole only after a whole status line (`Hend`), and then the reader has
delivered `connectAns`, or the status is the `400` answer's.
-/
module

public import Net.Spec.net.http.ReadResponse
public import Net.Proof.net.OpErrorMsg
public import Net.Spec.net.http.modelReadLine
public import Net.Spec.net.http.modelReadMIMEHeader
public import Perennial.Spec.strings.Cut
public import Perennial.Spec.strings.TrimLeft
public import Net.Spec.net.http.ParseHTTPVersion
public import Net.Spec.net.http.badStringError
public import Net.Spec.net.http.fixPragmaCacheControl
public import Net.Spec.net.http.readTransfer
public import Net.Proof.net.http.HdrLemmas
public import Perennial.Spec.strconv.Atoi
public import Perennial.Proof.github_com.mit_pdos.perennial.goose.model.strings.Base

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace net.http

section pure

theorem statusLine_no_nl : W8 10 ∉ statusLine := by decide

theorem proto_of_take : ∀ n, n < 33 →
    (cutByte (statusLine.take n) (W8 32)).2.2 = true →
      (cutByte (statusLine.take n) (W8 32)).1 = go!"HTTP/1.0" := by
  decide

/-- The status line's version, when its first space is in the part read. -/
theorem proto_of_prefix {line : List w8} (h : line <+: statusLine)
    (hok : (cutByte line (W8 32)).2.2 = true) : (cutByte line (W8 32)).1 = go!"HTTP/1.0" :=
  by
    have hl : line.length ≤ 32 := by simpa [statusLine] using h.length_le
    rw [List.prefix_iff_eq_take.mp h] at hok ⊢
    exact proto_of_take _ (by omega) hok

theorem badLine_no_nl : W8 10 ∉ badStatusLine ++ [W8 13] := by decide

theorem badReqAns_split : net.rpc.badReqAns =
    (badStatusLine ++ [W8 13]) ++ W8 10 :: (hdrWire badHdr [W8 13] ++ go!"400 Bad Request") := by
  decide

theorem connectAns_split : net.rpc.connectAns = statusLine ++ W8 10 :: [W8 10] := by decide

theorem proto_of_take_bad : ∀ n, n < 26 →
    (cutByte ((badStatusLine ++ [W8 13]).take n) (W8 32)).2.2 = true →
      (cutByte ((badStatusLine ++ [W8 13]).take n) (W8 32)).1 = go!"HTTP/1.1" := by
  decide

/-- The version of a status line of either answer, when its first space is in the part read. -/
theorem proto_of_prefix2 {line : List w8} (h : line <+: statusLine ∨ line <+: badStatusLine ++ [W8 13])
    (hok : (cutByte line (W8 32)).2.2 = true) :
    (cutByte line (W8 32)).1 = go!"HTTP/1.0" ∨ (cutByte line (W8 32)).1 = go!"HTTP/1.1" := by
  rcases h with h | h
  · exact Or.inl (proto_of_prefix h hok)
  · right
    have hl : line.length ≤ 25 := by simpa [badStatusLine] using h.length_le
    rw [List.prefix_iff_eq_take.mp h] at hok ⊢
    exact proto_of_take_bad _ (by omega) hok

theorem bad_status : (cutByte badStatusLine (W8 32)) = (go!"HTTP/1.1", go!"400 Bad Request", true) := by
  decide

theorem bad_status_ne : trimLeftByte go!"400 Bad Request" (W8 32) ≠ net.rpc.connectedStatus := by
  decide

end pure

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : net.http.Assumptions]

/-- A malformed header's error (`mimeErr`) has a property `L` of the stream's errors and of every
`errLeaf` error (`textproto.ProtocolError`). -/
theorem mimeErr_L (L : GoInterface → Prop) (hL : ∀ e, models_lab.errLeaf e → L e)
    (E : List w8 → GoInterface → IProp GF) (err : GoInterface) :
    (□ ∀ (r : List w8) (e : GoInterface), E r e -∗ ⌜L e⌝) ∗ mimeErr E err ⊢ ⌜L err⌝ := by
  iintro ⟨#HL, #Hm⟩
  unfold mimeErr
  icases Hm with (⟨%r, #HE⟩ | %Hp)
  · iapply HL $$ HE
  ipureintro
  obtain ⟨msg, rfl, -⟩ := Hp
  exact hL _ (Or.inr ⟨⟨_, _⟩, rfl, models_lab.noFmt_protocolError, Or.inr (Or.inr rfl)⟩)

theorem ReadResponse.wp_proof_errs
    (wp_ReadLine : modelReadLine.spec (GF := GF) (hG := hG))
    (wp_MIME : modelReadMIMEHeader.spec (GF := GF) (hG := hG))
    (wp_Cut : strings.Cut.spec (GF := GF) (hG := hG))
    (wp_Trim : strings.TrimLeft.spec (GF := GF) (hG := hG))
    (wp_Version : ParseHTTPVersion.spec (GF := GF) (hG := hG))
    (wp_bad : badStringError.spec (GF := GF) (hG := hG))
    (wp_pragma : fixPragmaCacheControl.spec (GF := GF) (hG := hG))
    (wp_transfer : readTransfer.spec (GF := GF) (hG := hG))
    (wp_Atoi : strconv.Atoi.spec (GF := GF) (hG := hG)) :
    ReadResponse.spec_errs (GF := GF) (hG := hG) := by
  intro L hL b ri S E req rq
  wp_start as ⟨#Henv, #Hstream, Hb, #Hlaw1, #Hlaw2, #Hlaw3, Hreq, %Hmeth, #HlawL⟩
  ihave #Hstr := httpEnv_strings $$ Henv
  ihave #Hbound : (□ ∀ r', S r' -∗ ⌜r'.length + 2 ^ 12 < 2 ^ 62⌝ : IProp GF) $$ []
  · imodintro
    iintro %r' HS
    ihave %h := Hlaw1 $$ HS
    ipureintro
    have h2 : rpc.connectAns.length = 34 := by decide
    have h3 : rpc.badReqAns.length = 103 := by decide
    rcases h with h | h
    · have h1 := h.length_le; omega
    · have h1 := h.length_le; omega
  wp_auto
  wp_apply wp_ReadLine b ri S E [] $$ Hstream Hbound [Hb] as %line %err ⟨%l, %Hl10, Hcase⟩
  · iexact Hb
  -- the line read: a whole status line, a prefix of one (cut by an error), or an error
  ihave Hu : ((⌜line = [] ∧ err ≠ GoInterface.nil ∧ _root_.Perennial.io.ptrTyped err ∧ L err⌝ ∗
        net.errStr err ∗ EtcdGrove.bufio.ownReader b ri S E l) ∨
      (⌜err = GoInterface.nil ∧ (line <+: statusLine ∨ line <+: badStatusLine ++ [W8 13])⌝ ∗
        ∃ rr : List w8, EtcdGrove.bufio.ownReader b ri S E rr ∗
        (⌜rr = statusLine ++ [W8 10] ∧ line = statusLine⌝ ∨
          ⌜rr = badStatusLine ++ [W8 13, W8 10] ∧ line = badStatusLine⌝ ∨
          (□ ∀ r', S r' -∗ ⌜rr <+: r' → r' = rr⌝))) : IProp GF)
      $$ [Hcase]
  · icases Hcase with (⟨⟨%Herr, %Hline⟩, Hb⟩ | ⟨%e, %He, #Hea, Hb, %Hcases⟩)
    · -- the whole line: one of the two status lines
      ihave ⟨%q, HS, Hcl⟩ := EtcdGrove.bufio.ownReader_open b ri S E _ $$ Hb
      ihave %Hp := Hlaw1 $$ HS
      ihave Hb := Hcl $$ HS
      simp only [List.nil_append] at Hp
      iright
      rcases Hp with Hp | Hp
      · have hl : l = statusLine := by
          refine prefix_nl Hl10 statusLine_no_nl (t := [W8 10]) ?_
          rw [← connectAns_split]
          exact (List.prefix_append _ _).trans Hp
        subst hl
        have hline : line = statusLine := by
          rw [Hline]; decide
        isplitr
        · ipureintro
          exact ⟨Herr, Or.inl (hline ▸ List.prefix_refl _)⟩
        iexists [] ++ statusLine ++ [W8 10]
        iframe Hb
        ileft
        ipureintro; exact ⟨by simp, hline⟩
      · have hl : l = badStatusLine ++ [W8 13] := by
          refine prefix_nl Hl10 badLine_no_nl
            (t := hdrWire badHdr [W8 13] ++ go!"400 Bad Request") ?_
          rw [← badReqAns_split]
          exact (List.prefix_append _ _).trans Hp
        subst hl
        have hline : line = badStatusLine := by
          rw [Hline]; decide
        isplitr
        · ipureintro
          exact ⟨Herr, Or.inr (hline ▸ List.prefix_append _ _)⟩
        iexists [] ++ (badStatusLine ++ [W8 13]) ++ [W8 10]
        iframe Hb
        iright; ileft
        ipureintro; exact ⟨by simp, hline⟩
    · rcases Hcases with ⟨hne, hnil, hline⟩ | ⟨hnil, herr, hline⟩
      · -- a line cut by an error: the stream stays there
        unfold EtcdGrove.io.errAt
        icases Hea with ⟨(%Hen | #HE), %Hty⟩
        · exact absurd Hen He
        ihave ⟨%q, HS, Hcl⟩ := EtcdGrove.bufio.ownReader_open b ri S E _ $$ Hb
        ihave %Hp := Hlaw1 $$ HS
        ihave Hb := Hcl $$ HS
        simp only [List.nil_append] at Hp
        have hls : l <+: statusLine ∨ l <+: badStatusLine ++ [W8 13] := by
          rcases Hp with Hp | Hp
          · left
            rw [connectAns_split] at Hp
            exact prefix_no_nl Hl10 statusLine_no_nl ((List.prefix_append _ _).trans Hp)
          · right
            rw [badReqAns_split] at Hp
            exact prefix_no_nl Hl10 badLine_no_nl ((List.prefix_append _ _).trans Hp)
        iright
        isplitr
        · ipureintro; exact ⟨hnil, hline ▸ hls⟩
        iexists [] ++ l
        iframe Hb
        iright; iright
        imodintro
        iintro %r' HS
        iapply Hlaw2 $$ %([] ++ l) %r' %e HE HS
      · -- nothing read: the error
        ileft
        unfold EtcdGrove.io.errAt at *
        icases Hea with ⟨(%Hen | #HE), %Hty⟩
        · exact absurd Hen He
        ihave #Hm := Hlaw3 $$ HE
        ihave %HLe := HlawL $$ HE
        rw [List.nil_append] at *
        subst herr
        iframe Hb Hm
        ipureintro
        exact ⟨hline, He, Hty, HLe⟩
  ihave #Henv' := Henv
  iunfold httpEnv at Henv'
  icases Henv' with ⟨#Hbufio, #Hio, #Hfmt, #Hstrconv, #Htok, %nb, #Hnb⟩
  ihave #Hinit := _root_.Perennial.io.isInit_access $$ Hio
  icases Hinit with ⟨-, -, -, -, #HEOF, #HUEOF, -⟩
  unfold errors.newVar
  icases HEOF with ⟨%xe, #Hxe, -⟩
  icases HUEOF with ⟨%xu, #Hxu, -, #Hxuw⟩
  ihave #Hxum := net.errStr_of_wp ⟨go.GoType.PointerType errors.errorString.ty, #xu⟩ _ $$ Hxuw
  icases Hu with (⟨%Hc, #Hm, Hb⟩ | ⟨⟨%Herr, %Hline⟩, %rr, Hb, Hk⟩)
  · -- nothing read: the error (`io.ErrUnexpectedEOF` for `io.EOF`)
    obtain ⟨-, Hne, Hty, HLe⟩ := Hc
    cases err with
    | nil => exact absurd rfl Hne
    | ok ei =>
    wp_auto
    by_cases hty : ei.ty = go.GoType.PointerType errors.errorString.ty
    · obtain ⟨l0, hl0⟩ := Hty ei _ rfl hty
      obtain ⟨ty, v⟩ := ei
      simp only at hty hl0
      subst hty hl0
      simp only [↓reduceIte]
      wp_auto
      wp_if_destruct
      · try wp_auto
        iapply HΦ
        ileft; iframe Hxum; ipureintro
        exact ⟨by simp [interface.mkOk], hL _ (models_lab.errLeaf_ptr _ _ models_lab.noFmt_errorString)⟩
      · try wp_auto
        iapply HΦ
        ileft; iframe Hm; ipureintro
        exact ⟨by simp, HLe⟩
    · simp only [hty, ↓reduceIte]
      try wp_auto
      iapply HΦ
      ileft; iframe Hm; ipureintro
      exact ⟨by simp, HLe⟩
  -- the header block to read: what follows the status line read
  ihave ⟨%hb, %eol, %rest, ⟨%Hhb, %Heol, %Hhbc⟩, #HL, #Hend⟩ : (∃ (hb : List HdrLine) (eol rest : List w8),
      ⌜hdrBlockOk hb ∧ (eol = [] ∨ eol = [W8 13]) ∧ (hb = [] ∨ hb = badHdr)⌝ ∗
      (□ ∀ r', S r' -∗ ⌜rr <+: r' → r' <+: rr ++ hdrWire hb eol ++ rest⌝) ∗
      (□ ∀ r', S r' -∗ ⌜rr ++ hdrWire hb eol <+: r' →
        rr ++ hdrWire hb eol = net.rpc.connectAns ∨ line = badStatusLine⌝) : IProp GF) $$ [Hk]
  · icases Hk with (⟨%Hrr, %Hl⟩ | ⟨%Hrr, %Hl⟩ | #Hcut)
    · subst Hrr
      iexists [], [], []
      isplitr
      · ipureintro; exact ⟨by decide, Or.inl rfl, Or.inl rfl⟩
      isplitr
      · imodintro
        iintro %r' HS
        ihave %h := Hlaw1 $$ HS
        ipureintro
        intro h1
        rcases h with h | h
        · simpa [hdrWire, connectAns_split] using h
        · exact absurd (h1.trans h) (by decide)
      · imodintro
        iintro %r' -
        ipureintro
        intro _
        left; decide
    · subst Hrr
      iexists badHdr, [W8 13], go!"400 Bad Request"
      isplitr
      · ipureintro; exact ⟨badHdr_ok, Or.inr rfl, Or.inr rfl⟩
      isplitr
      · imodintro
        iintro %r' HS
        ihave %h := Hlaw1 $$ HS
        ipureintro
        intro h1
        rcases h with h | h
        · exact absurd (h1.trans h) (by decide)
        · rw [badReqAns_split] at h
          simpa [List.append_assoc] using h
      · imodintro
        iintro %r' -
        ipureintro
        intro _
        right; exact Hl
    · iexists [], [], []
      isplitr
      · ipureintro; exact ⟨by decide, Or.inl rfl, Or.inl rfl⟩
      isplitr
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
  subst Herr
  wp_auto
  wp_apply wp_Cut line _ $$ [$Hstr]
  rw [cut_single]; try rw [show (32#8 : w8) = W8 32 from rfl]
  try wp_auto
  generalize hc : cutByte line (W8 32) = c
  obtain ⟨proto, st, ok⟩ := c
  simp only []
  cases ok
  · try wp_auto
    wp_apply wp_bad $$ Hfmt as %e ⟨-, %xb, %sb, %hxsb, #Hxsb⟩
    obtain ⟨rfl, -⟩ := hxsb
    ihave #Hbm := errorString_errStr xb sb $$ Hxsb
    try wp_auto
    iapply HΦ
    ileft; iframe Hbm; ipureintro
    exact ⟨by simp, hL _ (models_lab.errLeaf_ptr _ _ models_lab.noFmt_errorString)⟩
  have hproto : proto = go!"HTTP/1.0" ∨ proto = go!"HTTP/1.1" := by
    have := proto_of_prefix2 Hline (by rw [hc])
    rw [hc] at this; exact this
  try wp_auto
  wp_apply wp_Trim st _
  · ipureintro; intro b hb; simp at hb; subst hb; decide
  rw [trimLeft_single]; try rw [show (32#8 : w8) = W8 32 from rfl]
  try wp_auto
  wp_apply wp_Cut _ _ $$ [$Hstr]
  rw [cut_single]; try rw [show (32#8 : w8) = W8 32 from rfl]
  try wp_auto
  generalize cutByte (trimLeftByte st (W8 32)) (W8 32) = c2
  obtain ⟨code, c2b, c2c⟩ := c2
  simp only []
  try wp_auto
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len code with %Hcl
  try wp_auto
  wp_if_destruct
  rotate_left
  · try wp_auto
    wp_apply wp_bad $$ Hfmt as %e ⟨-, %xb, %sb, %hxsb, #Hxsb⟩
    obtain ⟨rfl, -⟩ := hxsb
    ihave #Hbm := errorString_errStr xb sb $$ Hxsb
    try wp_auto
    iapply HΦ
    ileft; iframe Hbm; ipureintro
    exact ⟨by simp, hL _ (models_lab.errLeaf_ptr _ _ models_lab.noFmt_errorString)⟩
  try wp_auto
  wp_apply wp_Atoi code $$ Hstrconv as %x %aerr -
  try wp_auto
  cases aerr with
  | ok ae =>
    simp only []
    try wp_auto
    wp_apply wp_bad $$ Hfmt as %e ⟨-, %xb, %sb, %hxsb, #Hxsb⟩
    obtain ⟨rfl, -⟩ := hxsb
    ihave #Hbm := errorString_errStr xb sb $$ Hxsb
    try wp_auto
    iapply HΦ
    ileft; iframe Hbm; ipureintro
    exact ⟨by simp, hL _ (models_lab.errLeaf_ptr _ _ models_lab.noFmt_errorString)⟩
  | nil =>
  simp only []
  try wp_auto
  wp_if_destruct
  · try wp_auto
    wp_apply wp_bad $$ Hfmt as %e ⟨-, %xb, %sb, %hxsb, #Hxsb⟩
    obtain ⟨rfl, -⟩ := hxsb
    ihave #Hbm := errorString_errStr xb sb $$ Hxsb
    try wp_auto
    iapply HΦ
    ileft; iframe Hbm; ipureintro
    exact ⟨by simp, hL _ (models_lab.errLeaf_ptr _ _ models_lab.noFmt_errorString)⟩
  try wp_auto
  wp_apply wp_Version proto as %vmaj %vmin %vok %Hvok
  · iframe Henv; ipureintro
    rcases hproto with h | h <;> rw [h]
    · exact Or.inl (List.prefix_refl _)
    · exact Or.inr (List.prefix_refl _)
  obtain ⟨Hvok1, -⟩ := Hvok
  obtain rfl : vok = true := by rw [Hvok1]; simpa using hproto
  try wp_auto
  wp_apply wp_MIME b ri S E rr hb eol rest (W64 9223372036854775807) Hhb Heol
      (by rcases Hhbc with rfl | rfl <;> decide) $$ Henv Hstream Hbound HL Hlaw2 [Hb]
    as %m %merr Hm
  · iexact Hb
  try wp_auto
  icases Hm with (⟨%Hme, #Hmerr, -⟩ | ⟨%Hmn, Hm, Hb⟩)
  · -- an error (`io.ErrUnexpectedEOF` for `io.EOF`)
    ihave #Hm := mimeErr_errStr E merr $$ [Hlaw3 Hmerr]
    · iframe Hlaw3 Hmerr
    obtain ⟨Hne, Hty⟩ := Hme
    ihave %HLe := mimeErr_L L hL E merr $$ [$HlawL $Hmerr]
    cases merr with
    | nil => exact absurd rfl Hne
    | ok ei =>
    try wp_auto
    by_cases hty : ei.ty = go.GoType.PointerType errors.errorString.ty
    · obtain ⟨l0, hl0⟩ := Hty ei _ rfl hty
      obtain ⟨ty, v⟩ := ei
      simp only at hty hl0
      subst hty hl0
      simp only [↓reduceIte]
      try wp_auto
      wp_if_destruct
      · try wp_auto
        iapply HΦ
        ileft; iframe Hxum; ipureintro
        exact ⟨by simp [interface.mkOk], hL _ (models_lab.errLeaf_ptr _ _ models_lab.noFmt_errorString)⟩
      · try wp_auto
        iapply HΦ
        ileft; iframe Hm; ipureintro
        exact ⟨by simp, HLe⟩
    · simp only [hty, ↓reduceIte]
      try wp_auto
      iapply HΦ
      ileft; iframe Hm; ipureintro
      exact ⟨by simp, HLe⟩
  subst Hmn
  ihave ⟨%ms, Hm, Hcv, %Habs⟩ := hdrOwn_open m hb $$ Hm
  have hk : ∀ k ∈ [go!"Pragma", go!"Transfer-Encoding", go!"Content-Length", go!"Trailer"],
      ms !! k = none := by
    intro k hk
    apply Habs
    rcases Hhbc with rfl | rfl
    · simp
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl <;> decide
  try wp_auto
  wp_apply wp_pragma m ms $$ [Hm] as Hm
  · iframe Hm; ipureintro; exact hk _ (by simp)
  try wp_auto
  wp_apply wp_transfer.1 «$r0_ptr» _ ms b req rq _ (W64 9223372036854775807)
      $$ [Henv «$r0» Hm Hcv Hreq]
    as ⟨%rv', %ms', Hrv, %Hst, Hm, -, -, Hreq⟩
  · isplitr
    · iexact Henv
    isplitl [«$r0»]
    · iexact «$r0»
    simp only []
    isplitl [Hm]
    · iexact Hm
    isplitl [Hcv]
    · iexact Hcv
    isplitr
    · ipureintro
      exact ⟨hk _ (by simp), hk _ (by simp), hk _ (by simp)⟩
    isplitr
    · ipureintro; trivial
    isplitl [Hreq]
    · iexact Hreq
    ipureintro
    rw [Hmeth]; decide
  try wp_auto
  iapply HΦ
  iright
  isplitr
  · ipureintro; rfl
  iexists rv'
  iframe Hrv
  by_cases hs : rv'.Status' = rpc.connectedStatus
  · ihave ⟨%q, HS, Hcl⟩ := EtcdGrove.bufio.ownReader_open b ri S E _ $$ Hb
    ihave %h := Hend $$ HS
    ihave Hb := Hcl $$ HS
    rcases h (List.prefix_append _ _) with h' | h'
    · iright
      isplitr
      · ipureintro; exact hs
      rw [← h']
      iexact Hb
    · exfalso
      subst h'
      rw [bad_status] at hc
      cases hc
      simp only at Hst
      exact bad_status_ne (Hst ▸ hs)
  · ileft; ipureintro; exact hs

/-- `ReadResponse.spec`, from `ReadResponse.spec_errs` with no property of the errors. -/
theorem ReadResponse.wp_proof
    (wp_ReadLine : modelReadLine.spec (GF := GF) (hG := hG))
    (wp_MIME : modelReadMIMEHeader.spec (GF := GF) (hG := hG))
    (wp_Cut : strings.Cut.spec (GF := GF) (hG := hG))
    (wp_Trim : strings.TrimLeft.spec (GF := GF) (hG := hG))
    (wp_Version : ParseHTTPVersion.spec (GF := GF) (hG := hG))
    (wp_bad : badStringError.spec (GF := GF) (hG := hG))
    (wp_pragma : fixPragmaCacheControl.spec (GF := GF) (hG := hG))
    (wp_transfer : readTransfer.spec (GF := GF) (hG := hG))
    (wp_Atoi : strconv.Atoi.spec (GF := GF) (hG := hG)) :
    ReadResponse.spec (GF := GF) (hG := hG) := by
  intro b ri S E req rq
  wp_start_folded as ⟨#Henv, #Hstream, Hb, #Hlaw1, #Hlaw2, #Hlaw3, Hreq, %Hmeth⟩
  wp_apply ReadResponse.wp_proof_errs wp_ReadLine wp_MIME wp_Cut wp_Trim wp_Version wp_bad
      wp_pragma wp_transfer wp_Atoi (fun _ => True) (fun _ _ => trivial) b ri S E req rq
      $$ [$Henv $Hstream $Hb $Hlaw1 $Hlaw2 $Hlaw3 $Hreq] as %resp %err Hpost
  · isplitr
    · ipureintro; exact Hmeth
    imodintro
    iintro %r %e -
    ipureintro; trivial
  iapply HΦ
  icases Hpost with (⟨%Hne, #Hs⟩ | H)
  · ileft; iframe Hs; ipureintro; exact Hne
  · iright; iexact H

end proof


section resp
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : net.http.Assumptions]

/-- **Trust-boundary axiom, interim**: `http.ReadResponse` meets `ReadResponse.spec_resp` (a stream of
responses; httpdriver). Interim, retired by phase 7's S5 (the client half: the model's head parser on
general heads, `readTransfer`, the body reader). -/
axiom ReadResponse.wp_proof_resp : ReadResponse.spec_resp (GF := GF) (hG := hG)

end resp

end net.http
end Perennial

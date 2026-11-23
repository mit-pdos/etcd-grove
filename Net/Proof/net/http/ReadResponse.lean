/-
`http.ReadResponse` on net/rpc's `CONNECT` answer (see `Net/Spec/net/http/ReadResponse.lean`).

The status line is read whole (`modelReadLine`, then the answer's bytes are a prefix of
`connectAns`, so the line is `statusLine`) or cut by an error, after which the stream stays where
it is (the finality law): either way the line is a prefix of `statusLine`, and the parse of it
either fails (`badStringError`, `Atoi`'s error) or finds the version `"HTTP/1.0"`
(`proto_of_prefix`). The header block is read over a law that its bytes are a prefix of the
position's `"\n"` (`modelReadMIMEHeader`); it is read whole only after a whole status line
(`Hlaw2`), and then the reader has delivered `connectAns`.
-/
module

public import Net.Spec.net.http.ReadResponse
public import Net.Spec.net.http.modelReadLine
public import Net.Spec.net.http.modelReadMIMEHeader
public import Net.Spec.net.http.modelCutByte
public import Net.Spec.net.http.modelTrimLeftByte
public import Net.Spec.net.http.ParseHTTPVersion
public import Net.Spec.net.http.badStringError
public import Net.Spec.net.http.fixPragmaCacheControl
public import Net.Spec.net.http.readTransfer
public import Perennial.Spec.strconv.Atoi
public import Perennial.Proof.github_com.mit_pdos.perennial.goose.model.strings.Base

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace net.http

section pure

/-- A line up to a `"\n"` of `s ++ "\n" ++ t` (`s` without one) is `s`. -/
theorem prefix_nl {l s t : List w8} (hl : W8 10 ∉ l) (hs : W8 10 ∉ s)
    (h : l ++ [W8 10] <+: s ++ W8 10 :: t) : l = s := by
  induction l generalizing s with
  | nil =>
    cases s with
    | nil => rfl
    | cons x s =>
      obtain ⟨u, hu⟩ := h
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at hu
      exact absurd (hu.1 ▸ List.mem_cons_self) hs
  | cons y l ih =>
    cases s with
    | nil =>
      obtain ⟨u, hu⟩ := h
      simp only [List.cons_append, List.nil_append, List.cons.injEq] at hu
      exact absurd (hu.1 ▸ List.mem_cons_self) hl
    | cons x s =>
      obtain ⟨u, hu⟩ := h
      simp only [List.cons_append, List.append_assoc, List.cons.injEq] at hu
      have hxy : y = x := hu.1
      subst hxy
      have := ih (fun h => hl (List.mem_cons_of_mem _ h)) (fun h => hs (List.mem_cons_of_mem _ h))
        ⟨u, by rw [List.append_assoc]; exact hu.2⟩
      rw [this]

/-- A prefix of `s ++ "\n" ++ t` without a `"\n"` is a prefix of `s` (`s` without one). -/
theorem prefix_no_nl {l s t : List w8} (hl : W8 10 ∉ l) (hs : W8 10 ∉ s)
    (h : l <+: s ++ W8 10 :: t) : l <+: s := by
  induction l generalizing s with
  | nil => exact List.nil_prefix
  | cons y l ih =>
    cases s with
    | nil =>
      obtain ⟨u, hu⟩ := h
      simp only [List.cons_append, List.nil_append, List.cons.injEq] at hu
      exact absurd (hu.1 ▸ List.mem_cons_self) hl
    | cons x s =>
      obtain ⟨u, hu⟩ := h
      simp only [List.cons_append, List.cons.injEq] at hu
      have hxy : y = x := hu.1
      subst hxy
      exact List.prefix_cons_inj _ |>.mpr
        (ih (fun h => hl (List.mem_cons_of_mem _ h)) (fun h => hs (List.mem_cons_of_mem _ h))
          ⟨u, hu.2⟩)

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

end pure

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : net.http.Assumptions]

theorem ReadResponse.wp_proof
    (wp_ReadLine : modelReadLine.spec (GF := GF) (hG := hG))
    (wp_MIME : modelReadMIMEHeader.spec (GF := GF) (hG := hG))
    (wp_Cut : modelCutByte.spec (GF := GF) (hG := hG))
    (wp_Trim : modelTrimLeftByte.spec (GF := GF) (hG := hG))
    (wp_Version : ParseHTTPVersion.spec (GF := GF) (hG := hG))
    (wp_bad : badStringError.spec (GF := GF) (hG := hG))
    (wp_pragma : fixPragmaCacheControl.spec (GF := GF) (hG := hG))
    (wp_transfer : readTransfer.spec (GF := GF) (hG := hG))
    (wp_Atoi : strconv.Atoi.spec (GF := GF) (hG := hG)) :
    ReadResponse.spec (GF := GF) (hG := hG) := by
  intro b ri S E req rq
  wp_start as ⟨#Henv, #Hstream, Hb, #Hlaw1, #Hlaw2, Hreq, %Hmeth⟩
  ihave #Hbound : (□ ∀ r', S r' -∗ ⌜r'.length + 2 ^ 12 < 2 ^ 62⌝ : IProp GF) $$ []
  · imodintro
    iintro %r' HS
    ihave %h := Hlaw1 $$ HS
    ipureintro
    have h1 := h.length_le
    have h2 : rpc.connectAns.length = 34 := by decide
    omega
  wp_auto
  wp_apply wp_ReadLine b ri S E [] $$ Hstream Hbound [Hb] as %line %err ⟨%l, %Hl10, Hcase⟩
  · iexact Hb
  -- the line read: `statusLine` (whole), a prefix of it (cut by an error), or an error
  ihave Hu : ((⌜line = [] ∧ err ≠ GoInterface.nil ∧ _root_.Perennial.io.ptrTyped err⌝ ∗
        EtcdGrove.bufio.ownReader b ri S E l) ∨
      (⌜err = GoInterface.nil ∧ line <+: statusLine⌝ ∗ ∃ rr : List w8,
        EtcdGrove.bufio.ownReader b ri S E rr ∗
        (□ ∀ r', S r' -∗ ⌜r' <+: rr ++ [W8 10]⌝) ∗
        (□ ∀ r', S r' -∗ ⌜rr ++ [W8 10] <+: r' → rr ++ [W8 10] = rpc.connectAns⌝)) : IProp GF)
      $$ [Hcase]
  · icases Hcase with (⟨⟨%Herr, %Hline⟩, Hb⟩ | ⟨%e, %He, #Hea, Hb, %Hcases⟩)
    · -- the whole line: `statusLine`
      ihave ⟨%q, HS, Hcl⟩ := EtcdGrove.bufio.ownReader_open b ri S E _ $$ Hb
      ihave %Hp := Hlaw1 $$ HS
      ihave Hb := Hcl $$ HS
      have hl : l = statusLine := by
        refine prefix_nl Hl10 statusLine_no_nl (t := [W8 10]) ?_
        rw [← connectAns_eq]
        simp only [List.nil_append] at Hp
        exact (List.prefix_append _ _).trans Hp
      subst hl
      iright
      isplitr
      · ipureintro
        refine ⟨Herr, ?_⟩
        rw [Hline, show dropCR statusLine = statusLine by decide]; exact List.prefix_refl _
      iexists [] ++ statusLine ++ [W8 10]
      iframe Hb
      isplitl []
      · imodintro
        iintro %r' HS
        ihave %h := Hlaw1 $$ HS
        ipureintro
        rw [connectAns_eq] at h
        simpa using h
      · imodintro
        iintro %r' -
        ipureintro
        intro _
        rw [connectAns_eq]; simp
    · rcases Hcases with ⟨hne, hnil, hline⟩ | ⟨hnil, herr, hline⟩
      · -- a line cut by an error: the stream stays there
        unfold EtcdGrove.io.errAt
        icases Hea with ⟨(%Hen | #HE), %Hty⟩
        · exact absurd Hen He
        ihave ⟨%q, HS, Hcl⟩ := EtcdGrove.bufio.ownReader_open b ri S E _ $$ Hb
        ihave %Hp := Hlaw1 $$ HS
        ihave Hb := Hcl $$ HS
        have hlp : l <+: rpc.connectAns := by
          simp only [List.nil_append] at Hp
          exact (List.prefix_append _ _).trans Hp
        have hls : l <+: statusLine := by
          rw [connectAns_eq] at hlp
          exact prefix_no_nl Hl10 statusLine_no_nl hlp
        -- after the error, every state is a prefix of `l`
        ihave #Hfin : (□ ∀ r', S r' -∗ ⌜r' <+: l⌝ : IProp GF) $$ []
        · imodintro
          iintro %r' HS
          ihave %h1 := Hlaw1 $$ HS
          ihave %h2 := Hlaw2 $$ %([] ++ l) %r' %e HE HS
          ipureintro
          simp only [List.nil_append] at h2
          rcases List.prefix_or_prefix_of_prefix h1 hlp with h | h
          · exact h
          · rw [h2 h]; exact List.prefix_refl _
        iright
        isplitr
        · ipureintro; exact ⟨hnil, hline ▸ hls⟩
        iexists [] ++ l
        iframe Hb
        isplitl []
        · imodintro
          iintro %r' HS
          ihave %h := Hfin $$ HS
          ipureintro
          simp only [List.nil_append]
          exact h.trans (List.prefix_append _ _)
        · imodintro
          iintro %r' HS
          ihave %h := Hfin $$ HS
          ipureintro
          intro h'
          simp only [List.nil_append] at h'
          have := (h'.trans h).length_le
          simp at this
          omega
      · -- nothing read: the error
        ileft
        unfold EtcdGrove.io.errAt at *
        icases Hea with ⟨-, %Hty⟩
        rw [List.nil_append] at *
        iframe Hb
        ipureintro
        exact ⟨hline, herr ▸ He, herr ▸ Hty⟩
  ihave #Henv' := Henv
  iunfold httpEnv at Henv'
  icases Henv' with ⟨#Hbufio, #Hio, #Hfmt, #Hstrconv, %nb, #Hnb⟩
  ihave #Hinit := _root_.Perennial.io.isInit_access $$ Hio
  icases Hinit with ⟨-, -, -, -, #HEOF, #HUEOF, -⟩
  unfold errors.newVar
  icases HEOF with ⟨%xe, #Hxe, -⟩
  icases HUEOF with ⟨%xu, #Hxu, -⟩
  icases Hu with (⟨%Hc, Hb⟩ | ⟨⟨%Herr, %Hline⟩, %rr, Hb, #HL1, #HL2⟩)
  · -- nothing read: the error (`io.ErrUnexpectedEOF` for `io.EOF`)
    obtain ⟨-, Hne, Hty⟩ := Hc
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
        ileft; ipureintro; simp [interface.mkOk]
      · try wp_auto
        iapply HΦ
        ileft; ipureintro; simp
    · simp only [hty, ↓reduceIte]
      try wp_auto
      iapply HΦ
      ileft; ipureintro; simp
  · subst Herr
    wp_auto
    wp_apply wp_Cut line (W8 32)
    try wp_auto
    generalize hc : cutByte line (W8 32) = c
    obtain ⟨proto, st, ok⟩ := c
    simp only []
    cases ok
    · try wp_auto
      wp_apply wp_bad $$ Hfmt as %e -
      try wp_auto
      iapply HΦ
      ileft; ipureintro; simp
    have hproto : proto = go!"HTTP/1.0" := by
      have := proto_of_prefix Hline (by rw [hc])
      rw [hc] at this; exact this
    subst hproto
    try wp_auto
    wp_apply wp_Trim
    try wp_auto
    wp_apply wp_Cut
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
      wp_apply wp_bad $$ Hfmt as %e -
      try wp_auto
      iapply HΦ
      ileft; ipureintro; simp
    try wp_auto
    wp_apply wp_Atoi code $$ Hstrconv as %x %aerr -
    try wp_auto
    cases aerr with
    | ok ae =>
      simp only []
      try wp_auto
      wp_apply wp_bad $$ Hfmt as %e -
      try wp_auto
      iapply HΦ
      ileft; ipureintro; simp
    | nil =>
    simp only []
    try wp_auto
    wp_if_destruct
    · try wp_auto
      wp_apply wp_bad $$ Hfmt as %e -
      try wp_auto
      iapply HΦ
      ileft; ipureintro; simp
    try wp_auto
    wp_apply wp_Version go!"HTTP/1.0"
    · ipureintro; exact Or.inl rfl
    try wp_auto
    wp_apply wp_MIME b ri S E rr (W64 9223372036854775807) $$ Hstream Hbound HL1 [Hb] as %m %merr Hm
    · iexact Hb
    try wp_auto
    icases Hm with (%Hme | ⟨%Hmn, Hm, Hb⟩)
    · -- an error (`io.ErrUnexpectedEOF` for `io.EOF`)
      obtain ⟨Hne, Hty⟩ := Hme
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
          ileft; ipureintro; simp [interface.mkOk]
        · try wp_auto
          iapply HΦ
          ileft; ipureintro; simp
      · simp only [hty, ↓reduceIte]
        try wp_auto
        iapply HΦ
        ileft; ipureintro; simp
    subst Hmn
    try wp_auto
    wp_apply wp_pragma m $$ Hm as Hm
    try wp_auto
    wp_apply wp_transfer «$r0_ptr» _ b req rq _ (W64 9223372036854775807) $$ [Henv «$r0» Hm Hreq]
      as ⟨%rv', Hrv, %Hst, Hm, Hreq⟩
    · isplitr
      · iexact Henv
      isplitl [«$r0»]
      · iexact «$r0»
      simp only []
      isplitl [Hm]
      · iexact Hm
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
    · iright
      isplitr
      · ipureintro; exact hs
      ihave ⟨%q, HS, Hcl⟩ := EtcdGrove.bufio.ownReader_open b ri S E _ $$ Hb
      ihave %h := HL2 $$ HS
      ihave Hb := Hcl $$ HS
      have h' : rr ++ [W8 10] = rpc.connectAns := h (List.prefix_append _ _)
      rw [← h']
      iexact Hb
    · ileft; ipureintro; exact hs

end proof

end net.http
end Perennial

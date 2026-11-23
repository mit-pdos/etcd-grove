/-
The proof of `modelReadMIMEHeader` (`Net/Spec/net/http/modelReadMIMEHeader.lean`): the stream's next
bytes are a prefix of `"\n"`, so the first `Peek(1)` (`Spec/bufio/Reader__Peek.lean`) sees `'\n'` or
fails, and the first `modelReadLine` (`Net/Spec/net/http/modelReadLine.lean`) returns an empty line
(the `"\n"`) or an error: the loop's body runs once and returns, its header-line path unreachable.
-/
module

public import Net.Spec.net.http.modelReadMIMEHeader
public import Net.Spec.net.http.modelReadLine
public import Spec.bufio.Reader__Peek

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace net.http

/-- A prefix of `r ++ [x]` that extends `r ++ l ++ ys` with `l` not empty is `r ++ [x]` itself,
and `l = [x]`. -/
theorem mime_prefix_one (r l ys : List w8) (x : w8) (hl : l ≠ [])
    (h : r ++ l ++ ys <+: r ++ [x]) : l = [x] ∧ ys = [] := by
  rw [List.append_assoc] at h
  have h2 := (List.prefix_append_right_inj r).1 h
  obtain ⟨t, ht⟩ := h2
  cases l with
  | nil => exact absurd rfl hl
  | cons a l' =>
    simp only [List.cons_append, List.cons.injEq] at ht
    obtain ⟨rfl, ht⟩ := ht
    have : l' ++ ys ++ t = [] := by simpa [List.append_assoc] using ht
    simp only [List.append_eq_nil_iff] at this
    exact ⟨by rw [this.1.1], this.1.2⟩

theorem mime_len_one (s : GoSlice) (h : [c].length = sint.nat s.len) :
    0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z s.len := by
  simp only [List.length_singleton] at h
  constructor
  · decide
  · have : sint.nat s.len = 1 := h.symm
    revert this; word

/-- A stream state `r ++ c :: q` within `r ++ "\n"`: `c` is `'\n'`. -/
theorem mime_peek_nl (r : List w8) (c : w8) (q : List w8) (h : r ++ c :: q <+: r ++ [W8 10]) :
    c = W8 10 := by
  have h2 := (List.prefix_append_right_inj r).1 h
  obtain ⟨t, ht⟩ := h2
  simp only [List.cons_append, List.cons.injEq] at ht
  exact ht.1

/-- No line of a byte or more, without `'\n'`, is in the stream when it is within `r ++ "\n"`. -/
theorem mime_no_line (r l q : List w8) (hl : l ≠ []) (hn : W8 10 ∉ l)
    (h : r ++ (l ++ q) <+: r ++ [W8 10]) : False := by
  have h' : r ++ l ++ q <+: r ++ [W8 10] := by simpa [List.append_assoc] using h
  obtain ⟨hl1, -⟩ := mime_prefix_one r l q (W8 10) hl h'
  exact hn (by rw [hl1]; simp)

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : net.http.Assumptions]

set_option goose.wp.extras true

set_option hygiene false in
/-- The loop, from the reader at `r` (`Hb`): its first `modelReadLine` returns the empty line or
an error, and the loop returns. -/
local macro "mime_loop" : tactic => `(tactic| (
  ihave HI : ("Hb" ∷ EtcdGrove.bufio.ownReader b ri S E r : IProp GF) $$ [Hb]
  · iexact Hb
  wp_for HI
  try simp only [decide_true, ↓reduceIte]
  try wp_auto
  ihave #HRL := wp_modelReadLine b ri S E r $$ Hrd HSb
  wp_apply HRL $$ Hb as %line %err ⟨%l, %Hl, (⟨⟨%Herr, %Hline⟩, Hb⟩ | ⟨%e, %He, #HE, Hb, %Hc⟩)⟩
  · subst Herr Hline
    rcases l with _ | ⟨a, l'⟩
    · rw [show dropCR ([] : List w8) = [] from rfl]
      try wp_auto
      wp_apply (github_com.mit_pdos.perennial.goose.model.strings.wp_string_len
        (t := go.string) []) as %-
      try wp_auto
      wp_for_post
      iapply HΦ
      iright
      iframe Hmp
      simp only [List.append_nil]
      iframe Hb
      try (ipureintro; rfl)
    · icases EtcdGrove.bufio.ownReader_open b ri S E _ $$ Hb with ⟨%q', HS, -⟩
      ihave %Hp := HSp $$ HS
      exact (mime_no_line r (a :: l') ([W8 10] ++ q') (List.cons_ne_nil _ _) Hl
        (by simp only [List.append_assoc] at Hp ⊢; exact Hp)).elim
  · rcases l with _ | ⟨a, l'⟩
    · obtain ⟨rfl, rfl⟩ : err = e ∧ line = [] := by
        rcases Hc with ⟨h, _⟩ | ⟨_, h1, h2⟩
        · exact absurd rfl h
        · exact ⟨h1, h2⟩
      obtain ⟨i, rfl⟩ : ∃ i, err = GoInterface.ok i := by
        cases err with
        | nil => exact absurd rfl He
        | ok i => exact ⟨i, rfl⟩
      iunfold EtcdGrove.io.errAt at HE
      icases HE with ⟨-, %Hty⟩
      try wp_auto
      wp_for_post
      iapply HΦ
      ileft
      ipureintro; exact ⟨He, Hty⟩
    · icases EtcdGrove.bufio.ownReader_open b ri S E _ $$ Hb with ⟨%q', HS, -⟩
      ihave %Hp := HSp $$ HS
      exact (mime_no_line r (a :: l') q' (List.cons_ne_nil _ _) Hl
        (by simp only [List.append_assoc] at Hp ⊢; exact Hp)).elim))

theorem modelReadMIMEHeader.wp_proof
    (wp_Peek : EtcdGrove.bufio.Reader.Peek.spec (GF := GF) (hG := hG))
    (wp_modelReadLine : modelReadLine.spec (GF := GF) (hG := hG)) :
    modelReadMIMEHeader.spec (GF := GF) (hG := hG) := by
  intro b ri S E r maxH
  iintro #Hrd #HSb #HSp
  wp_start as Hb
  wp_auto
  rw [go.make1_underlying, go.is_underlying (t := net.textproto.MIMEHeader.ty)]
  wp_apply (wp_map_make1 (K := GoString) (V := GoSlice)) as %mp Hmp
  try wp_auto
  ihave #HPk := wp_Peek b ri S E r $$ Hrd HSb
  wp_apply HPk $$ Hb as %s %err (⟨%Herr, %c, %q, %e, Hs, Hback⟩ | ⟨%Herr, #HE, Hb⟩)
  · subst Herr
    ihave %Hsl := ownSlice_len $$ Hs
    have h0 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z s.len := mime_len_one s Hsl.1
    -- the peeked byte is the stream's next, `'\n'`
    ihave Hnl : (s ↦* [c] -∗ ⌜c = W8 10⌝ ∗ EtcdGrove.bufio.ownReader b ri S E r) $$ [Hback]
    · iintro Hs
      ihave Hbb := Hback $$ Hs
      icases EtcdGrove.bufio.ownReaderBuf_open b ri S E r (c :: q) e $$ Hbb with ⟨HS, Hcl⟩
      ihave %Hp := HSp $$ HS
      ihave Hbb := Hcl $$ HS
      isplitl []
      · ipureintro; exact mime_peek_nl r c q Hp
      iapply (EtcdGrove.bufio.ownReader_buf b ri S E r).2
      iexists (c :: q), e
      iexact Hbb
    wp_auto
    rw [ite_eq_left_of_eq_true _ _ (eq_true h0)]
    wp_apply (wp_load_slice_index s (sint.Z (W64 0)) [c] (DFrac.own 1) c (by decide)) $$ [Hs] as Hs
    · iframe; ipureintro; rfl
    try wp_auto
    wp_if_destruct
    · icases Hnl $$ Hs with ⟨%hc, -⟩
      exact absurd hc (by decide)
    · rw [ite_eq_left_of_eq_true _ _ (eq_true h0)]
      wp_apply (wp_load_slice_index s (sint.Z (W64 0)) [c] (DFrac.own 1) c (by decide)) $$ [Hs] as Hs
      · iframe; ipureintro; rfl
      try wp_auto
      wp_if_destruct
      · icases Hnl $$ Hs with ⟨%hc, -⟩
        exact absurd hc (by decide)
      · icases Hnl $$ Hs with ⟨%hc, Hb⟩
        subst hc
        try wp_auto
        mime_loop
  · obtain ⟨i, rfl⟩ : ∃ i, err = GoInterface.ok i := by
      cases err with
      | nil => exact absurd rfl Herr
      | ok i => exact ⟨i, rfl⟩
    try wp_auto
    mime_loop

end proof

end net.http
end Perennial

/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/client/BufioErr.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`bufio.Writer`'s sticky error, without the protocol: `WriteByte` and `Write` on a writer whose
error is set write nothing and return the error, so they need no `□ Q (...)` (the harness's
`wp_WriteByte`/`wp_Write` ask for it in every case: notes/hub-requests.md, HUB-REQUEST 6).
Proved from the harness's `bufio` code (an unfold of the harness's package, listed in
notes/prove-clientpkg.md).
-/
module


-- PORT: lab imports dropped: Harness.Proof.bufio.Writer, Harness.Proof.bufio.Reader

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace bufio

section proofs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [bufio.Assumptions]

set_option goose.wp.extras true

theorem wp_WriteByte_err (bw : Loc) (wr : GoInterface) (J Q : List w8 → IProp GF)
    (sent pend : List w8) (err : GoInterface) (c : w8) (herr : err ≠ interface.nil) :
    {{ ownWriter bw wr J Q sent pend err }}
      (App (Val (bw @!! go.GoType.PointerType bufio.Writer.ty @!! go!"WriteByte")) (Val #c))
    {{ RET #err; ownWriter bw wr J Q sent pend err }} := by
  wp_start as Hown
  iunfold ownWriter, writerRep at Hown
  icases Hown with ⟨HJ, #HQ, %buf, %n, %rest, Hb, Hbuf, %Hn, #Herr⟩
  rcases err with ei | _
  · wp_auto
    iapply HΦ
    iunfold ownWriter, writerRep
    iframe HJ HQ
    iexists buf, n, rest
    iframe Hb Hbuf Herr
    ipureintro; exact Hn
  · exact absurd rfl herr

theorem wp_Write_err (bw : Loc) (wr : GoInterface) (J Q : List w8 → IProp GF)
    (sent pend : List w8) (err : GoInterface) (p : GoSlice) (dq : DFrac) (ps : List w8)
    (herr : err ≠ interface.nil) :
    {{ ownWriter bw wr J Q sent pend err ∗ p ↦*{dq} ps }}
      (App (Val (bw @!! go.GoType.PointerType bufio.Writer.ty @!! go!"Write")) (Val #p))
    {{ (nn : w64), RET (PairV #nn #err); p ↦*{dq} ps ∗ ownWriter bw wr J Q sent pend err }} := by
  wp_start as ⟨Hown, Hp⟩
  iunfold ownWriter, writerRep at Hown
  icases Hown with ⟨HJ, #HQ, %buf, %n, %rest, Hb, Hbuf, %Hn, #Herr⟩
  rcases err with ei | _
  · wp_auto
    wp_for
    wp_apply wp_Writer_Available $$ Hb as Hb
    wp_if_destruct <;>
    · try wp_auto
      iapply HΦ
      iframe Hp
      iunfold ownWriter, writerRep
      iframe HJ HQ
      iexists buf, n, rest
      iframe Hb Hbuf Herr
      ipureintro; exact Hn
  · exact absurd rfl herr

/-- `ReadByte` with its error well formed (`errWf`: comparable with `io.EOF`), the harness's
`wp_ReadByte`'s proof with the error's `errWf` kept (notes/spec-feedback.md). -/
theorem wp_ReadByte_wf (br : Loc) (rd : GoInterface) (I : List w8 → IProp GF) (R : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ readerOk rd I ∗ ownReader br rd I R }}
      (App (Val (br @!! go.GoType.PointerType bufio.Reader.ty @!! go!"ReadByte")) (Val #()))
    {{ (c : w8) (err : GoInterface), RET (PairV #c #err);
        (⌜err = interface.nil⌝ ∗ ownReader br rd I (R ++ [c])) ∨
        (⌜err ≠ interface.nil ∧ errWf err⌝ ∗ net.rpc.errAny err ∗ ownReader br rd I R) }} := by
  wp_start as ⟨#Hrd, Hown⟩
  ihave #Hrd' := Hrd
  iunfold readerOk at Hrd'
  icases Hrd' with ⟨%e, %He, -⟩
  obtain ⟨rfl, hty⟩ := He
  iunfold ownReader, readerRep at Hown
  icases Hown with ⟨%pend, %perr, HI, %buf, %r, %w, %lb, %lrs, %pre, %post, Hb, Hbuf, %Hrw, #Herr⟩
  wp_auto
  ihave HL : (∃ (pend : List w8) (perr : GoInterface) (buf : GoSlice) (r w lb lrs : w64)
      (pre post : List w8),
      "HI" ∷ I (R ++ pend) ∗
      "Hb" ∷ br ↦ bufio.Reader.mk buf (interface.ok e) r w perr lb lrs ∗
      "Hbuf" ∷ buf ↦* (pre ++ pend ++ post) ∗
      "%Hrw" ∷ ⌜sint.Z r = pre.length ∧ sint.Z w = pre.length + pend.length ∧
        0 < (pre ++ pend ++ post).length⌝ ∗ "#Herr" ∷ errOrNil perr : IProp GF) $$ [HI Hb Hbuf]
  · iexists pend, perr, buf, r, w, lb, _, pre, post
    iframe
    isplitr
    · ipureintro; exact Hrw
    iexact Herr
  wp_for HL
  ihave %Hlen := ownSlice_len _ _ _ $$ Hbuf
  have h63 : sint.Z buf.len < 2 ^ 63 := by word
  have hl : ((pre ++ pend ++ post).length : Int) = sint.Z buf.len := by
    rw [Hlen.1]; exact Int.toNat_of_nonneg Hlen.2
  simp only [List.length_append] at hl
  wp_if_destruct
  · -- nothing buffered
    subst Hif
    have hp : pend = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hp
    rcases perr with ep | _
    · -- a pending error: return it
      wp_auto
      wp_apply wp_readErr $$ Hb as Hb
      wp_for_post
      iapply HΦ
      iright
      unfold errOrNil
      icases Herr with (%Hn | ⟨#Ha, %Hwf⟩)
      · cases Hn
      iframe Ha
      isplitr
      · ipureintro; exact ⟨by simp, Hwf⟩
      iunfold ownReader, readerRep
      iexists [], interface.nil
      rw [List.append_nil]
      iframe HI
      iexists buf, r, r, lb, lrs, pre, post
      iframe Hbuf Hb
      isplitr
      · ipureintro; exact Hrw
      iunfold errOrNil; ileft; ipureintro; rfl
    · wp_auto
      isimp only [List.append_nil] at HI
      wp_apply wp_fill br e I R buf r lb lrs (pre ++ [] ++ post) (by simp at hl ⊢; omega)
        (by simp at Hrw ⊢; omega) $$ [$Hpkg $Hrd $HI $Hb $Hbuf] as ⟨%pend', %perr', -, HI, Hrep⟩
      wp_for_post
      iunfold readerRep at Hrep
      icases Hrep with ⟨%buf', %r', %w', %lb', %lrs', %pre', %post', Hb, Hbuf, %Hrw', #Herr'⟩
      iframe
      iexists pend', perr', buf', r', w', lb', lrs', pre', post'
      iframe
      isplitr
      · ipureintro; exact Hrw'
      iexact Herr'
  · -- a byte is buffered: return it
    obtain ⟨c, rest, rfl⟩ : ∃ c rest, pend = c :: rest := by
      cases pend with
      | nil =>
        exfalso; apply Hif; apply BitVec.eq_of_toInt_eq
        show sint.Z r = sint.Z w
        simp at Hrw; omega
      | cons c rest => exact ⟨c, rest, rfl⟩
    simp only [List.length_cons] at hl
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by omega, by omega⟩)]
    wp_apply wp_load_slice_index buf (sint.Z r) (pre ++ c :: rest ++ post) _ c (by omega)
      $$ [$Hbuf] as Hbuf
    · ipureintro
      rw [Hrw.1]
      simp
    have hr1 : sint.Z (r + W64 1) = (pre ++ [c]).length := by
      simp only [List.length_append, List.length_singleton]
      have : sint.Z (W64 1) = 1 := rfl
      word
    iapply HΦ
    ileft
    isplitr
    · ipureintro; rfl
    iunfold ownReader, readerRep
    iexists rest, perr
    rw [show R ++ [c] ++ rest = R ++ c :: rest by simp]
    iframe HI
    iexists buf, r + W64 1, w, W64 (uint.Z c), lrs, pre ++ [c], post
    rw [show pre ++ [c] ++ rest ++ post = pre ++ c :: rest ++ post by simp]
    iframe Hbuf Hb Herr
    ipureintro
    refine ⟨hr1, ?_, ?_⟩
    · simp at Hrw ⊢; omega
    · simp; omega

end proofs

end bufio

end Perennial

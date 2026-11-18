/-
The specs of `bufio.Reader` (Go's code, `Harness/Code/bufio.lean`) over an underlying
`io.Reader` given by its spec (`readerOk`, `Defs.lean`), and their proofs.

* `NewReader(rd)`: a fresh `*Reader` over `rd` that has returned nothing and buffers nothing
  (`ownReader br rd I R` from `I R`).
* `(*Reader).ReadByte()`: the next byte `c` of the stream (`R ++ [c]` returned), or an error
  with some message and nothing returned.
* `(*Reader).Read(p)`: the next bytes `data` of the stream (at most `len(p)`) in `p`'s first
  `n = len(data)` elements, and an error `nil` or with some message (bytes and an error may come
  together, as the underlying reader's).
-/
module

public import Harness.Proof.bufio.Defs
public import Harness.Proof.net.rpc.Wire

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode NetConn

namespace bufio

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- The suffix `buf[w:]` of a buffer holding `pre ++ rest` with `w = len(pre)`, and the way
back with any `rest'` of `rest`'s length. -/
theorem suffix_acc (buf : GoSlice) (w : w64) (pre rest : List w8)
    (hw : sint.Z w = pre.length) :
    (buf ↦* (pre ++ rest) : IProp GF) ⊢
      ⌜sint.Z buf.len = pre.length + rest.length⌝ ∗
      slice.slice buf w8 w buf.len ↦* rest ∗
      (∀ rest' : List w8, ⌜rest'.length = rest.length⌝ -∗
        slice.slice buf w8 w buf.len ↦* rest' -∗ buf ↦* (pre ++ rest')) := by
  iintro Hb
  ihave %Hl := ownSlice_len _ _ _ $$ Hb
  have h63 : sint.Z buf.len < 2 ^ 63 := by word
  have hl : pre.length + rest.length = (sint.Z buf.len).toNat := by
    rw [← List.length_append]; exact Hl.1
  have hw' : w = W64 pre.length := by
    apply BitVec.eq_of_toInt_eq
    rw [show BitVec.toInt w = sint.Z w from rfl, hw]
    have : ((pre.length : Int) : w64).toInt = (pre.length : Int) := by
      rw [BitVec.toInt_intCast]; apply Int.bmod_eq_of_le
      · omega
      · omega
    exact this.symm
  subst hw'
  ihave ⟨%Hsz, Hsuf, Hback⟩ := net.rpc.ownSlice_drop_acc buf _ pre rest $$ Hb
  iframe Hsuf Hback
  ipureintro; exact Hsz.2

/-- `ownSlice_trivial_slice` with the literal `0`. -/
theorem whole_slice (s : GoSlice) (dq : DFrac) (vs : List w8) :
    (s ↦*{dq} vs : IProp GF) ⊣⊢ slice.slice s w8 0 s.len ↦*{dq} vs := by
  rw [show (0 : w64) = W64 0 from rfl]; exact ownSlice_trivial_slice s dq vs

/-- `io.ErrNoProgress` holds an error with some message, an `*errorString`. -/
theorem errNoProgress_errAny [io.Assumptions] :
    isPkgInit (PROP := IProp GF) pkg_id.io ⊢
      ∃ e : GoInterface, globalAddr io.ErrNoProgress ↦□ e ∗ net.rpc.errAny e ∗ ⌜errWf e⌝ := by
  iintro #Hio
  ihave #Hi := io.isInit_access $$ Hio
  icases Hi with ⟨-, -, -, -, -, -, #HNP, -⟩
  ihave #HNP' := HNP
  iunfold errors.newVar at HNP'
  icases HNP' with ⟨%x, #Hx, -⟩
  ihave ⟨%e, #He, #Hm, -⟩ := net.rpc.newVar_errMsg' _ _ $$ HNP
  icombine He Hx gives %Heq
  iexists e
  iframe He
  isplitl
  · iapply net.rpc.errMsg_errAny; iexact Hm
  ipureintro
  subst Heq
  intro e' h T _
  cases h
  exact ⟨x, rfl⟩

end lemmas

section proofs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [bufio.Assumptions]

set_option goose.wp.extras true

theorem wp_readErr (br : Loc) (v : bufio.Reader) :
    {{ (br ↦ v : IProp GF) }}
      (App (Val (br @!! go.GoType.PointerType bufio.Reader.ty @!! go!"readErr")) (Val #()))
    {{ RET #v.err'; br ↦ { v with err' := interface.nil } }} := by
  wp_start as Hb
  wp_auto
  iapply HΦ $$ Hb

theorem wp_reset (br : Loc) (v : bufio.Reader) (buf : GoSlice) (rd : GoInterface) :
    {{ (br ↦ v : IProp GF) }}
      (App (App (Val (br @!! go.GoType.PointerType bufio.Reader.ty @!! go!"reset")) (Val #buf))
        (Val #rd))
    {{ RET #(); br ↦ bufio.Reader.mk buf rd 0 0 interface.nil (W64 (-1)) (W64 (-1)) }} := by
  wp_start as Hb
  wp_auto
  iapply HΦ $$ Hb

/-- `fill()` with nothing buffered (`r = w`) and no pending error: reads into the buffer until
the underlying reader returns a byte or an error (or `io.ErrNoProgress` after 100 empty
reads). -/
theorem wp_fill (br : Loc) (e : GoInterfaceOk) (I : List w8 → IProp GF) (R : List w8)
    (buf : GoSlice) (r lb lrs : w64) (bs : List w8)
    (hr : 0 ≤ sint.Z r ∧ sint.Z r ≤ bs.length) (hbs : 0 < bs.length) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ readerOk (interface.ok e) I ∗ I R ∗
        br ↦ bufio.Reader.mk buf (interface.ok e) r r interface.nil lb lrs ∗ buf ↦* bs }}
      (App (Val (br @!! go.GoType.PointerType bufio.Reader.ty @!! go!"fill")) (Val #()))
    {{ RET #(); ∃ (pend : List w8) (perr : GoInterface),
        ⌜pend ≠ [] ∨ perr ≠ interface.nil⌝ ∗ I (R ++ pend) ∗
        readerRep br (interface.ok e) pend perr }} := by
  wp_start as ⟨#Hrd, HI, Hb, Hbuf⟩
  unfold readerOk
  icases Hrd with ⟨%e', %He, #Hrd⟩
  obtain ⟨he, hty⟩ := He
  cases he
  ihave %Hlen := ownSlice_len _ _ _ $$ Hbuf
  ihave %Hwf := ownSlice_wf _ _ _ $$ Hbuf
  have hl : (bs.length : Int) = sint.Z buf.len := by
    rw [Hlen.1]; exact Int.toNat_of_nonneg Hlen.2
  wp_auto
  wp_if_destruct
  -- `r > 0`: slide the (empty) buffered part to the front
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨hr.1, Int.le_refl _, by omega⟩)]
  wp_apply wp_slice_copy_of_len_zero (V := w8) buf (slice.slice buf w8 r r) (by simp [slice.slice])
  isimp at Hb
  ihave Hb : (br ↦ bufio.Reader.mk buf (interface.ok e) 0 0 interface.nil lb lrs : IProp GF) $$ [Hb]
  · iexact Hb
  rotate_left
  -- `r = 0`
  have : r = 0 := by
    apply BitVec.eq_of_toInt_eq
    show sint.Z r = sint.Z 0
    rw [show sint.Z (0 : w64) = 0 from rfl]
    rw [show sint.Z (W64 0) = 0 from rfl] at *; omega
  subst this
  all_goals
    wp_if_destruct
    · exfalso
      have h0 : sint.Z (0 : w64) = 0 := rfl
      have h0' : sint.Z (0#64) = 0 := rfl
      (try simp only [BitVec.sub_self] at *)
      omega
    ihave #Hio := io_init_of_bufio $$ Hpkg
    ihave ⟨%enp, #Henp, #Hnp, %Hnpwf⟩ := errNoProgress_errAny $$ Hio
    ihave HL : (∃ (i : w64) (bs' : List w8), "i" ∷ i_ptr ↦ i ∗
        "Hb" ∷ br ↦ bufio.Reader.mk buf (interface.ok e) 0 0 interface.nil lb lrs ∗
        "Hbuf" ∷ buf ↦* bs' ∗ "HI" ∷ I R ∗ "%Hbs" ∷ ⌜bs'.length = bs.length⌝ : IProp GF)
      $$ [i Hb Hbuf HI]
    · iexists _, bs; iframe; ipureintro; rfl
    wp_for HL
    have h0 : sint.Z (0 : w64) = 0 := rfl
    have hbs' : (bs'.length : Int) = sint.Z buf.len := by omega
    wp_if_destruct
    · rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨Int.le_refl _, by omega, Hwf.2⟩)]
      ihave Hsl := (whole_slice buf _ bs').1 $$ Hbuf
      wp_auto
      wp_apply Hrd $$ HI Hsl as %data %err %Hd Hsl HI #Herr
      ihave Hbuf := (whole_slice buf _ _).2 $$ Hsl
      have h63 : sint.Z buf.len < 2 ^ 63 := by word
      have hdl : data.length < 2 ^ 63 := by omega
      have hZ : sint.Z (W64 data.length) = data.length := sint_Z_W64_length hdl
      have hW0 : sint.Z (W64 0) = 0 := rfl
      wp_if_destruct
      · exfalso; omega
      have hw : sint.Z (0 + W64 data.length) = data.length := by
        simpa using hZ
      rcases err with ei | _
      · -- an error: keep it pending, return
        wp_auto
        wp_for_post
        iapply HΦ
        iexists data, interface.ok ei
        iframe HI
        isplitr
        · ipureintro; right; simp
        unfold readerRep
        iexists buf, 0, 0 + W64 data.length, lb, lrs, [], bs'.drop data.length
        simp only [List.nil_append, List.length_nil, List.length_append,
          List.length_drop]
        iframe Hb Hbuf Herr
        ipureintro
        exact ⟨h0, by rw [hw]; simp, by omega⟩
      · wp_auto
        wp_if_destruct
        · -- a byte read: return
          wp_for_post
          iapply HΦ
          iexists data, interface.nil
          iframe HI
          isplitr
          · ipureintro; left; intro h; subst h; simp at Hif
          unfold readerRep
          iexists buf, 0, 0 + W64 data.length, lb, lrs, [], bs'.drop data.length
          simp only [List.nil_append, List.length_nil, List.length_append,
            List.length_drop]
          iframe Hb Hbuf Herr
          ipureintro
          exact ⟨h0, by rw [hw]; simp, by omega⟩
        · -- nothing read: try again
          have hd : data = [] := by
            apply List.eq_nil_of_length_eq_zero; omega
          subst hd
          wp_for_post
          (try isimp at Hb)
          iframe
          iexists (i - W64 1), bs'
          simp only [List.append_nil, List.nil_append, List.length_nil, List.drop_zero]
          iframe HI Hbuf i
          isplitl [Hb]
          · (try isimp); iexact Hb
          ipureintro; exact Hbs
    · -- 100 empty reads: `io.ErrNoProgress`
      have hP : ¬ (sint.Z (W64 0) < sint.Z i) := by
        first | exact Hif | (intro h; apply Hif; simp [h])
      (try simp only [decide_eq_false hP, decide_true, ↓reduceIte])
      (try wp_auto)
      ihave %Hne := net.rpc.errAny_ne_nil _ $$ Hnp
      iapply HΦ
      iexists [], enp
      rw [List.append_nil]
      iframe HI
      isplitr
      · ipureintro; right; exact Hne
      unfold readerRep errOrNil
      iexists buf, 0, 0, lb, lrs, [], bs'
      simp only [List.nil_append, List.length_nil, List.append_nil]
      iframe Hb Hbuf
      isplitr
      · ipureintro; exact ⟨h0, by simp, by omega⟩
      iright; iframe Hnp; ipureintro; exact Hnpwf

theorem wp_NewReader (rd : GoInterface) (I : List w8 → IProp GF) (R : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ readerOk rd I ∗ I R }}
      (App (Val (@! bufio.NewReader)) (Val #rd))
    {{ (br : Loc), RET #br; ownReader br rd I R }} := by
  wp_start as ⟨#Hrd, HI⟩
  unfold readerOk
  icases Hrd with ⟨%e, %He, #Hrd⟩
  obtain ⟨rfl, hty⟩ := He
  wp_auto
  wp_func_call
  wp_call
  wp_auto
  simp only [hty, ↓reduceIte, decide_false]
  wp_auto
  wp_func_call
  wp_call
  wp_apply (wp_slice_make2 (V := w8) (W64 4096)) as %buf ⟨Hbuf, -⟩
  · ipureintro; decide
  wp_apply wp_reset $$ [$«$r0»] as Hr
  iapply HΦ
  unfold ownReader readerRep
  iexists [], interface.nil
  rw [List.append_nil]
  iframe HI
  iexists buf, 0, 0, W64 (-1), W64 (-1), [], List.replicate 4096 (zero_val w8)
  simp only [List.nil_append, List.length_nil, List.append_nil, List.length_replicate]
  iframe Hr Hbuf
  isplitr
  · ipureintro; exact ⟨rfl, rfl, by decide⟩
  unfold errOrNil
  ileft; ipureintro; rfl

/-- `ReadByte()`: see the file header. -/
theorem wp_ReadByte (br : Loc) (rd : GoInterface) (I : List w8 → IProp GF) (R : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ readerOk rd I ∗ ownReader br rd I R }}
      (App (Val (br @!! go.GoType.PointerType bufio.Reader.ty @!! go!"ReadByte")) (Val #()))
    {{ (c : w8) (err : GoInterface), RET (PairV #c #err);
        (⌜err = interface.nil⌝ ∗ ownReader br rd I (R ++ [c])) ∨
        (⌜err ≠ interface.nil⌝ ∗ net.rpc.errAny err ∗ ownReader br rd I R) }} := by
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
      icases Herr with (%Hn | ⟨#Ha, -⟩)
      · cases Hn
      iframe Ha
      isplitr
      · ipureintro; simp
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

/-- `Buffered()`: `w - r`. -/
theorem wp_Buffered (br : Loc) (v : bufio.Reader) :
    {{ (br ↦ v : IProp GF) }}
      (App (Val (br @!! go.GoType.PointerType bufio.Reader.ty @!! go!"Buffered")) (Val #()))
    {{ RET #(v.w' - v.r'); br ↦ v }} := by
  wp_start as Hb
  wp_auto
  iapply HΦ $$ Hb

/-- `Read(p)`: see the file header. -/
theorem wp_Read (br : Loc) (rd : GoInterface) (I : List w8 → IProp GF) (R : List w8)
    (p : GoSlice) (ps : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ readerOk rd I ∗ ownReader br rd I R ∗
        p ↦* ps }}
      (App (Val (br @!! go.GoType.PointerType bufio.Reader.ty @!! go!"Read")) (Val #p))
    {{ (n : w64) (err : GoInterface), RET (PairV #n #err);
        ∃ data : List w8, ⌜n = W64 data.length ∧ data.length ≤ ps.length⌝ ∗
        p ↦* (data ++ ps.drop data.length) ∗ ownReader br rd I (R ++ data) ∗ errOrNil err }} := by
  wp_start as ⟨#Hrd, Hown, Hp⟩
  ihave #Hrd' := Hrd
  iunfold readerOk at Hrd'
  icases Hrd' with ⟨%e, %He, #HRead⟩
  obtain ⟨rfl, hty⟩ := He
  iunfold ownReader, readerRep at Hown
  icases Hown with ⟨%pend, %perr, HI, %buf, %r, %w, %lb, %lrs, %pre, %post, Hb, Hbuf, %Hrw, #Herr⟩
  ihave %Hplen := ownSlice_len _ _ _ $$ Hp
  ihave %Hlen := ownSlice_len _ _ _ $$ Hbuf
  have h63 : sint.Z buf.len < 2 ^ 63 := by word
  have hl : ((pre ++ pend ++ post).length : Int) = sint.Z buf.len := by
    rw [Hlen.1]; exact Int.toNat_of_nonneg Hlen.2
  have hpl : (ps.length : Int) = sint.Z p.len := by
    rw [Hplen.1]; exact Int.toNat_of_nonneg Hplen.2
  simp only [List.length_append] at hl
  wp_auto
  wp_if_destruct
  · -- `len(p) = 0`
    have hps : ps = [] := List.eq_nil_of_length_eq_zero (by
      have : sint.Z p.len = 0 := by rw [Hif]; rfl
      omega)
    subst hps
    wp_apply wp_Buffered $$ Hb as Hb
    wp_if_destruct
    · iapply HΦ
      iexists []
      simp only [List.append_nil, List.length_nil, List.drop_nil]
      iframe Hp
      isplitr
      · ipureintro; exact ⟨rfl, Nat.le_refl _⟩
      isplitl
      · iunfold ownReader, readerRep
        iexists pend, perr
        iframe HI
        iexists buf, r, w, lb, lrs, pre, post
        iframe Hb Hbuf Herr
        ipureintro; exact Hrw
      iunfold errOrNil; ileft; ipureintro; rfl
    · wp_apply wp_readErr $$ Hb as Hb
      iapply HΦ
      iexists []
      simp only [List.append_nil, List.length_nil, List.drop_nil]
      iframe Hp Herr
      isplitr
      · ipureintro; exact ⟨rfl, Nat.le_refl _⟩
      iunfold ownReader, readerRep
      iexists pend, interface.nil
      iframe HI
      iexists buf, r, w, lb, lrs, pre, post
      iframe Hb Hbuf
      isplitr
      · ipureintro; exact Hrw
      iunfold errOrNil; ileft; ipureintro; rfl
  have hps : ps ≠ [] := by
    intro h; subst h; apply Hif; apply BitVec.eq_of_toInt_eq
    show sint.Z p.len = sint.Z (W64 0)
    simp at hpl; rw [← hpl]; rfl
  wp_if_destruct
  -- nothing buffered
  subst Hif
  have hp : pend = [] := List.eq_nil_of_length_eq_zero (by omega)
  subst hp
  rcases perr with ep | _
  · -- a pending error: return it
    wp_auto
    wp_apply wp_readErr $$ Hb as Hb
    iapply HΦ
    iexists []
    simp only [List.append_nil, List.nil_append, List.length_nil, List.drop_zero]
    iframe Hp Herr
    isplitr
    · ipureintro; exact ⟨rfl, Nat.zero_le _⟩
    iunfold ownReader, readerRep
    iexists [], interface.nil
    rw [List.append_nil R]
    iframe HI
    iexists buf, r, r, lb, lrs, pre, post
    rw [List.append_nil pre]
    iframe Hb Hbuf
    isplitr
    · ipureintro; simpa using Hrw
    iunfold errOrNil; ileft; ipureintro; rfl
  have hp63 : sint.Z p.len < 2 ^ 63 := by word
  wp_auto
  wp_if_destruct
  · -- a large read: straight into `p`
    isimp only [List.append_nil] at HI
    wp_apply HRead $$ HI Hp as %data %err %Hd Hp HI #Herr2
    isimp at Hb
    have hdl : data.length < 2 ^ 63 := by omega
    have hZ : sint.Z (W64 data.length) = data.length := sint_Z_W64_length hdl
    have hW0 : sint.Z (W64 0) = 0 := rfl
    wp_if_destruct
    · exfalso; omega
    wp_if_destruct
    · -- `n > 0`: `lastByte = p[n-1]`
      have hpos : 0 < data.length := by omega
      have hi : sint.Z (W64 data.length - W64 1) = data.length - 1 := by
        have : sint.Z (W64 1) = 1 := rfl
        word
      have hpl' : ((data ++ ps.drop data.length).length : Int) = sint.Z p.len := by
        simp; omega
      rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by omega, by omega⟩)]
      wp_apply wp_load_slice_index p (sint.Z (W64 data.length - W64 1)) _ _
        (data[data.length - 1]'(by omega)) (by omega) $$ [$Hp] as Hp
      · ipureintro
        rw [hi, show ((data.length : Int) - 1).toNat = data.length - 1 by omega,
          List.getElem?_append_left (by omega)]
        simp
      wp_apply wp_readErr $$ Hb as Hb
      iapply HΦ
      iexists data
      iframe Hp Herr2
      isplitr
      · ipureintro; exact ⟨rfl, Hd⟩
      iunfold ownReader, readerRep
      iexists [], interface.nil
      rw [List.append_nil (R ++ data)]
      iframe HI
      iexists buf, r, r, _, _, pre, post
      iframe Hb Hbuf
      isplitr
      · ipureintro; exact Hrw
      iunfold errOrNil; ileft; ipureintro; rfl
    · wp_apply wp_readErr $$ Hb as Hb
      iapply HΦ
      iexists data
      iframe Hp Herr2
      isplitr
      · ipureintro; exact ⟨rfl, Hd⟩
      iunfold ownReader, readerRep
      iexists [], interface.nil
      rw [List.append_nil (R ++ data)]
      iframe HI
      iexists buf, r, r, _, _, pre, post
      iframe Hb Hbuf
      isplitr
      · ipureintro; exact Hrw
      iunfold errOrNil; ileft; ipureintro; rfl
  -- one read into the buffer, then copy
  isimp only [List.append_nil] at HI
  wp_apply HRead $$ HI Hbuf as %data %err %Hd Hbuf HI #Herr2
  isimp at Hb
  simp only [List.length_append, List.length_nil, Nat.add_zero] at Hd hl
  have hdl : data.length < 2 ^ 63 := by omega
  have hZ : sint.Z (W64 data.length) = data.length := sint_Z_W64_length hdl
  have hW0 : sint.Z (W64 0) = 0 := rfl
  wp_if_destruct
  · exfalso; omega
  wp_if_destruct
  · -- nothing read
    have hd : data = [] := List.eq_nil_of_length_eq_zero (by
      have := congrArg (fun x : w64 => sint.Z x) Hif; omega)
    subst hd
    wp_apply wp_readErr $$ Hb as Hb
    iapply HΦ
    iexists []
    simp only [List.nil_append, List.length_nil, List.drop_zero]
    iframe Hp Herr2
    isplitr
    · ipureintro; exact ⟨rfl, Nat.zero_le _⟩
    iunfold ownReader, readerRep
    iexists [], interface.nil
    simp only [List.append_nil]
    iframe HI
    iexists buf, _, _, _, _, [], pre ++ post
    simp only [List.nil_append]
    iframe Hb Hbuf
    isplitr
    · ipureintro; simp at Hrw ⊢; omega
    iunfold errOrNil; ileft; ipureintro; rfl
  -- something read: the common state
  have hne : data ≠ [] := by
    intro h; subst h; exact Hif rfl
  generalize hw0 : (0#64 + W64 data.length : w64) = w0
  generalize hr0 : (0#64 : w64) = r0
  ihave Hst : (∃ (pend : List w8) (perr : GoInterface) (r w : w64) (pre post : List w8),
      "HI" ∷ I (R ++ pend) ∗
      "Hb" ∷ br ↦ bufio.Reader.mk buf (interface.ok e) r w perr lb lrs ∗
      "Hbuf" ∷ buf ↦* (pre ++ pend ++ post) ∗
      "%Hrw" ∷ ⌜sint.Z r = pre.length ∧ sint.Z w = pre.length + pend.length ∧
        0 < (pre ++ pend ++ post).length ∧ pend ≠ [] ∧ r = r0 ∧ w = w0⌝ ∗
      "#Herr" ∷ errOrNil perr : IProp GF)
    $$ [HI Hb Hbuf]
  · iexists data, err, r0, w0, [], (pre ++ [] ++ post).drop data.length
    simp only [List.nil_append]
    iframe HI Hb Hbuf Herr2
    ipureintro
    refine ⟨?_, ?_, ?_, hne, ?_⟩
    · subst hr0; rfl
    · subst hw0; simpa using hZ
    · simp at Hrw ⊢; omega
    · simp
  clear Hif Hd hZ hdl hl Hrw hne hw0 hr0
  icases Hst with ⟨%pend, %perr, %r, %w, %pre, %post, HI, Hb, Hbuf, %Hrw, #Herr⟩
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := Hrw
  subst r0 w0
  have Hrw := And.intro h1 (And.intro h2 (And.intro h3 h4))
  clear h1 h2 h3 h4
  rotate_left
  -- something buffered: the common state
  have hne : pend ≠ [] := by
    intro h; subst h; apply Hif; apply BitVec.eq_of_toInt_eq
    show sint.Z r = sint.Z w
    simp at Hrw; omega
  replace Hrw : sint.Z r = pre.length ∧ sint.Z w = pre.length + pend.length ∧
      0 < (pre ++ pend ++ post).length ∧ pend ≠ [] := ⟨Hrw.1, Hrw.2.1, Hrw.2.2, hne⟩
  all_goals
    ihave %Hlen2 := ownSlice_len _ _ _ $$ Hbuf
    ihave %Hwf2 := ownSlice_wf _ _ _ $$ Hbuf
    have hl2 : ((pre ++ pend ++ post).length : Int) = sint.Z buf.len := by
      rw [Hlen2.1]; exact Int.toNat_of_nonneg Hlen2.2
    simp only [List.length_append] at hl2
    obtain ⟨hr, hw, -, hne'⟩ := Hrw
    have hpos : 0 < pend.length := List.length_pos_iff.mpr hne'
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by omega, by omega, by omega⟩)]
    ihave ⟨Hsub, Hback⟩ := net.rpc.ownSlice_sub_acc (V := w8) r w buf (DFrac.own 1)
      (pre ++ pend ++ post) ⟨by omega, by omega, by omega⟩ $$ Hbuf
    have hsub : subslice (sint.nat r) (sint.nat w) (pre ++ pend ++ post) = pend := by
      rw [subslice_def, show sint.nat w = (pre ++ pend).length by
          show (sint.Z w).toNat = _; simp; omega, List.append_assoc, ← List.append_assoc pre,
        List.take_left, show sint.nat r = pre.length by show (sint.Z r).toNat = _; omega,
        List.drop_left]
    rw [hsub]
    wp_apply wp_slice_copy (V := w8) p ps (slice.slice buf w8 r w) pend (DFrac.own 1)
      $$ [$Hp $Hsub] as %n ⟨%Hn, Hp, Hsub⟩
    ihave Hbuf := Hback $$ Hsub
    have hpsl : 0 < ps.length := List.length_pos_iff.mpr hps
    have hk : sint.Z n = (min ps.length pend.length : Nat) := by
      have : (sint.Z n).toNat = min ps.length pend.length := Hn
      omega
    have hrn : sint.Z (r + n - W64 1) = pre.length + (min ps.length pend.length : Nat) - 1 := by
      have : sint.Z (W64 1) = 1 := rfl
      word
    have hrn' : sint.Z (r + n) = pre.length + (min ps.length pend.length : Nat) := by word
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by omega, by omega⟩)]
    wp_apply wp_load_slice_index buf (sint.Z (r + n - W64 1)) _ _
      (pend[min ps.length pend.length - 1]'(by omega)) (by omega) $$ [$Hbuf] as Hbuf
    · ipureintro
      rw [hrn, show ((pre.length : Int) + (min ps.length pend.length : Nat) - 1).toNat =
          pre.length + (min ps.length pend.length - 1) by omega, List.append_assoc,
        List.getElem?_append_right (by omega), List.getElem?_append_left (by omega)]
      simp
    isimp at Hb
    iapply HΦ
    iexists pend.take ps.length
    have hdl : (pend.take ps.length).length = min ps.length pend.length := List.length_take
    have hdrop : ps.drop pend.length = ps.drop (pend.take ps.length).length := by
      rw [hdl]
      by_cases h : pend.length ≤ ps.length
      · rw [Nat.min_eq_right h]
      · rw [List.drop_eq_nil_of_le (by omega), List.drop_eq_nil_of_le (by omega)]
    rw [← hdrop]
    iframe Hp
    isplitr
    · ipureintro
      refine ⟨?_, by omega⟩
      apply BitVec.eq_of_toInt_eq
      show sint.Z n = sint.Z (W64 _)
      rw [hk, sint_Z_W64_length (by omega), hdl]
    isplitl
    · iunfold ownReader, readerRep
      iexists pend.drop ps.length, perr
      rw [List.append_assoc R, List.take_append_drop]
      iframe HI
      iexists buf, r + n, w, _, _, pre ++ pend.take ps.length, post
      rw [show pre ++ pend.take ps.length ++ pend.drop ps.length ++ post = pre ++ pend ++ post by
        rw [List.append_assoc pre, List.take_append_drop]]
      iframe Hb Hbuf Herr
      ipureintro
      simp only [List.length_append, List.length_drop, hdl] at hl2 ⊢
      omega
    iunfold errOrNil; ileft; ipureintro; rfl

end proofs

end bufio

end Perennial

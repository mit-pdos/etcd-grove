/-
The specs of `io.ReadAtLeast` and `io.ReadFull` (Go's code, `Harness/Code/io_extra.lean`, under
`io.ExtraAssumptions`), generic over the reader's `Read` spec (`readsOk`), and that spec for a
`*bufio.Reader` (`bufioReadsOk`, from `wp_Read`) and for a connection (`readsOk_conn`).

* `readsOk rd I` (persistent): `readerOk`'s `Read` spec of the non-nil `io.Reader` `rd`, without
  `readerOk`'s condition that `rd` not be a `*bufio.Reader` (which only `NewReader` needs).
* `ReadAtLeast(rd, buf, min)` (`min ≤ len(buf)`): reads into `buf` until it has at least `min`
  bytes or the reader fails: the next bytes `data` of the stream in `buf`'s first
  `n = len(data)` elements; the error is `nil` exactly when `min ≤ n`, and otherwise has some
  message (the reader's error, or `io.ErrUnexpectedEOF`).
* `ReadFull(rd, buf)`: `ReadAtLeast(rd, buf, len(buf))`: `err = nil` exactly when
  `n = len(buf)`.
-/
module

public import Harness.Proof.bufio.Net
public import Harness.Code.io_extra

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode NetConn

namespace bufio

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- The `Read` spec of the `io.Reader` `rd` over `I`: see the file header (persistent). -/
def readsOk (rd : GoInterface) (I : List w8 → IProp GF) : IProp GF :=
  iprop(∃ e : GoInterfaceOk, ⌜rd = interface.ok e⌝ ∗
    □ ∀ (b : GoSlice) (bs : List w8) (R : List w8) (Φ : val → IProp GF),
      I R -∗ b ↦* bs -∗
      ▷ (∀ (data : List w8) (err : GoInterface), ⌜data.length ≤ bs.length⌝ -∗
          b ↦* (data ++ bs.drop data.length) -∗ I (R ++ data) -∗ errOrNil err -∗
          Φ (PairV #(W64 data.length) #err)) -∗
      WP (App (Val #(methods e.ty go!"Read" e.v)) (Val #b)) {{ Φ }})

instance readsOk_persistent (rd : GoInterface) (I : List w8 → IProp GF) :
    Persistent (readsOk (GF := GF) rd I) := by
  unfold readsOk; infer_instance

theorem readerOk_readsOk (rd : GoInterface) (I : List w8 → IProp GF) :
    readerOk (GF := GF) rd I ⊢ readsOk rd I := by
  unfold readerOk readsOk
  iintro ⟨%e, %He, #H⟩
  iexists e
  isplitr
  · ipureintro; exact He.1
  iexact H

end defs

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

variable [errors.Assumptions]

/-- A variable made by `errors.New` holds an error with some message, an `*errorString`. -/
theorem newVar_errOrNil (X msg : GoString) :
    errors.newVar (GF := GF) X msg ⊢
      ∃ e : GoInterface, globalAddr X ↦□ e ∗ errOrNil e ∗ ⌜e ≠ interface.nil⌝ := by
  iintro #HNP
  ihave #HNP' := HNP
  iunfold errors.newVar at HNP'
  icases HNP' with ⟨%x, #Hx, -⟩
  ihave ⟨%e, #He, #Hm, -⟩ := net.rpc.newVar_errMsg' _ _ $$ HNP
  icombine He Hx gives %Heq
  subst Heq
  iexists _
  iframe He
  isplitl
  · iunfold errOrNil; iright
    isplitl
    · iapply net.rpc.errMsg_errAny; iexact Hm
    ipureintro
    intro e' h T _
    cases h
    exact ⟨x, rfl⟩
  ipureintro; simp [interface.mkOk]

end lemmas

section proofs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- A `*bufio.Reader` (as an `io.Reader`) reads its stream: `readsOk` over `ownReader`. -/
theorem bufioReadsOk [bufio.Assumptions] (br : Loc) (rd : GoInterface)
    (I : List w8 → IProp GF) :
    (isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ readerOk rd I) ⊢
      readsOk (interface.mkOk (go.GoType.PointerType bufio.Reader.ty) #br) (ownReader br rd I) := by
  iintro ⟨#Hpkg, #Hrd⟩
  unfold readsOk
  iexists interface.mk (go.GoType.PointerType bufio.Reader.ty) #br
  isplitr
  · ipureintro; rfl
  imodintro
  iintro %b %bs %R %Φ Hown Hb HΦ
  wp_apply wp_Read br rd I R b bs $$ [$Hpkg $Hrd $Hown $Hb] as %n %err ⟨%data, %Hd, Hb, Hown, #He⟩
  obtain ⟨rfl, hdl⟩ := Hd
  iapply HΦ $$ %data %err %hdl Hb Hown He

/-- A connection (as an `io.Reader`) reads its stream, with the end's reader token. -/
theorem readsOk_conn [HasExt netConnExt] [net.Assumptions] [net.model.Assumptions]
    (cv : GoInterface) (cid : w64) (side : Bool) (P : Proto GF) :
    (isPkgInit (PROP := IProp GF) pkg_id.net ∗ net.rpc.connIface cv cid side) ⊢
      readsOk cv (recvTok cid side P) := by
  iintro H
  iapply readerOk_readsOk
  iapply readerOk_conn $$ H

variable [io.Assumptions] [io.ExtraAssumptions]

set_option hygiene false in
/-- `ReadAtLeast`'s return with the reader's error `ok ei` and `n < min` bytes. -/
local macro "readatleast_keep" : tactic => `(tactic| (
  (try wp_auto)
  iapply HΦ
  iexists data
  iframe Hb HI Hev
  ipureintro
  refine ⟨?_, hdl, ⟨(fun h => by cases h), (fun h => by omega)⟩⟩
  apply BitVec.eq_of_toInt_eq
  show sint.Z nv = sint.Z (W64 data.length)
  rw [hnv, sint_Z_W64_length (by omega)]))

set_option goose.wp.extras true

/-- `ReadAtLeast(rd, buf, min)`: see the file header. -/
theorem wp_ReadAtLeast (rd : GoInterface) (I : List w8 → IProp GF) (R : List w8)
    (buf : GoSlice) (bs : List w8) (min : w64) (hmin : sint.Z min ≤ bs.length) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.io ∗ readsOk rd I ∗ I R ∗ buf ↦* bs }}
      (App (App (App (Val (@! io.ReadAtLeast)) (Val #rd)) (Val #buf)) (Val #min))
    {{ (n : w64) (err : GoInterface), RET (PairV #n #err);
        ∃ data : List w8, ⌜n = W64 data.length ∧ data.length ≤ bs.length ∧
          (err = interface.nil ↔ sint.Z min ≤ data.length)⌝ ∗
        buf ↦* (data ++ bs.drop data.length) ∗ I (R ++ data) ∗ errOrNil err }} := by
  wp_start as ⟨#Hrd, HI, Hb⟩
  ihave #Hrd' := Hrd
  iunfold readsOk at Hrd'
  icases Hrd' with ⟨%e, %He, #HRead⟩
  subst He
  ihave %Hlen := ownSlice_len _ _ _ $$ Hb
  ihave %Hwf := ownSlice_wf _ _ _ $$ Hb
  have h63 : sint.Z buf.len < 2 ^ 63 := by word
  have hl : (bs.length : Int) = sint.Z buf.len := by
    rw [Hlen.1]; exact Int.toNat_of_nonneg Hlen.2
  have hW0 : sint.Z (W64 0) = 0 := rfl
  ihave #Hio := io.isInit_access $$ Hpkg
  icases Hio with ⟨-, -, -, -, #HEOF, #HUEOF, -⟩
  ihave ⟨%ue, #Hue, #Hueo, %Hune⟩ := newVar_errOrNil _ _ $$ HUEOF
  iunfold errors.newVar at HEOF
  icases HEOF with ⟨%eofx, #HEOF, -⟩
  wp_auto
  wp_if_destruct
  · exfalso; omega
  ihave HL : (∃ (data : List w8) (nv : w64) (ev : GoInterface),
      "n" ∷ n_ptr ↦ nv ∗ "err" ∷ err_ptr ↦ ev ∗ "Hb" ∷ buf ↦* (data ++ bs.drop data.length) ∗
      "HI" ∷ I (R ++ data) ∗ "#Hev" ∷ errOrNil ev ∗
      "%Hd" ∷ ⌜sint.Z nv = data.length ∧ data.length ≤ bs.length⌝ : IProp GF)
    $$ [n err Hb HI]
  · iexists [], _, _
    simp only [List.nil_append, List.length_nil, List.drop_zero, List.append_nil]
    iframe n err Hb HI
    isplitr
    · iunfold errOrNil; ileft; ipureintro; rfl
    ipureintro; exact ⟨rfl, Nat.zero_le _⟩
  wp_for HL
  obtain ⟨hnv, hdl⟩ := Hd
  wp_if_destruct
  · -- `n < min`
    rcases ev with ei | _
    · -- an error: done
      wp_auto
      simp only [goose_wp_simp_extra, Bool.false_eq_true, ↓reduceIte]
      wp_auto
      wp_if_destruct
      · exfalso; omega
      ihave #Hev' := Hev
      iunfold errOrNil at Hev'
      icases Hev' with (%Hn | ⟨-, %Hewf⟩)
      · cases Hn
      wp_if_destruct
      · -- `n > 0`: `err == EOF`?
        by_cases hty : ei.ty = go.GoType.PointerType errors.errorString.ty
        · obtain ⟨l, hl⟩ := Hewf ei rfl _ hty
          simp only [hty, ↓reduceIte]
          rw [hl]
          wp_auto
          wp_if_destruct
          · -- `io.EOF`: `io.ErrUnexpectedEOF`
            iapply HΦ
            iexists data
            iframe Hb HI Hueo
            ipureintro
            refine ⟨?_, hdl, ⟨(fun h => absurd h Hune), (fun h => by omega)⟩⟩
            apply BitVec.eq_of_toInt_eq
            show sint.Z nv = sint.Z (W64 data.length)
            rw [hnv, sint_Z_W64_length (by omega)]
          readatleast_keep
        simp only [hty, ↓reduceIte]
        wp_auto
        readatleast_keep
      readatleast_keep
    wp_auto
    simp only [goose_wp_simp_extra, ↓reduceIte]
    wp_auto
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by omega, by omega, Hwf.2⟩)]
    ihave ⟨%Hsz, Hsuf, Hback⟩ := suffix_acc buf nv data (bs.drop data.length) hnv $$ Hb
    wp_auto
    wp_apply HRead $$ HI Hsuf as %d2 %e2 %Hd2 Hsuf HI #He2
    ihave Hb := Hback $$ %_ %(by simp; simp at Hd2; omega) Hsuf
    wp_for_post
    iframe
    iexists data ++ d2, _, e2
    have hlist : data ++ (d2 ++ (bs.drop data.length).drop d2.length) =
        data ++ d2 ++ bs.drop (data ++ d2).length := by
      simp [List.drop_drop, List.append_assoc]
    rw [hlist, List.append_assoc R]
    iframe Hb HI He2 n err
    ipureintro
    simp only [List.length_drop, List.length_append] at Hd2 ⊢
    have : sint.Z (W64 d2.length) = d2.length := sint_Z_W64_length (by omega)
    constructor
    · word
    · omega
  -- `n ≥ min`
  wp_if_destruct
  · iapply HΦ
    iexists data
    iframe Hb HI
    isplitr
    · ipureintro
      refine ⟨?_, hdl, ⟨(fun _ => by omega), (fun _ => rfl)⟩⟩
      apply BitVec.eq_of_toInt_eq
      show sint.Z nv = sint.Z (W64 data.length)
      rw [hnv, sint_Z_W64_length (by omega)]
    iunfold errOrNil; ileft; ipureintro; rfl
  exfalso; omega

/-- `ReadFull(rd, buf)`: see the file header. -/
theorem wp_ReadFull (rd : GoInterface) (I : List w8 → IProp GF) (R : List w8)
    (buf : GoSlice) (bs : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.io ∗ readsOk rd I ∗ I R ∗ buf ↦* bs }}
      (App (App (Val (@! io.ReadFull)) (Val #rd)) (Val #buf))
    {{ (n : w64) (err : GoInterface), RET (PairV #n #err);
        ∃ data : List w8, ⌜n = W64 data.length ∧ data.length ≤ bs.length ∧
          (err = interface.nil ↔ data.length = bs.length)⌝ ∗
        buf ↦* (data ++ bs.drop data.length) ∗ I (R ++ data) ∗ errOrNil err }} := by
  wp_start as ⟨#Hrd, HI, Hb⟩
  ihave %Hlen := ownSlice_len _ _ _ $$ Hb
  have hl : (bs.length : Int) = sint.Z buf.len := by
    rw [Hlen.1]; exact Int.toNat_of_nonneg Hlen.2
  wp_auto
  wp_apply wp_ReadAtLeast rd I R buf bs buf.len (by omega) $$ [$Hpkg $Hrd $HI $Hb]
    as %n %err ⟨%data, %Hd, Hb, HI, #He⟩
  iapply HΦ
  iexists data
  iframe Hb HI He
  ipureintro
  obtain ⟨h1, h2, h3⟩ := Hd
  refine ⟨h1, h2, ?_⟩
  rw [h3]; omega

end proofs

end bufio

end Perennial

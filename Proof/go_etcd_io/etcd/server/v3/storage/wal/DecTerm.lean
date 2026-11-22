/- Lean-first (no Rocq counterpart).

# `errors.Is` returns on `io.EOF` and `io.ErrUnexpectedEOF` (`errIsTerm`)

Both are `*errorString` leaves (`errors.newVar`, `io`'s initialization), so `errors.Is(_, u)` on them returns
for every pointer target `u` (`errors.wp_Is_leaf`): what `Decode`'s `decUe` needs of its stops that return
them (ledger 2026-11-14, "no `errors.Is(_, io.ErrUnexpectedEOF)` termination"; `wal-vsnap3`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.wal.DecLemmas
public import Perennial.Proof.errors.Results
public import Proof.errors.NewVar
public import Proof.errors.ErrIsTerm
public import Proof.errors.ErrTree

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode

section term
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [bufio_sem : _root_.Perennial.bufio.Assumptions]
variable [errs_sem : _root_.Perennial.errors.Assumptions]

/-- **`io.EOF`'s and `io.ErrUnexpectedEOF`'s `errors.Is` return** (`decEnv`'s `io` initialization). -/
theorem decEnv_term (IoE : GoInterface → Prop) (eof ueof : GoInterface) :
    decEnv (GF := GF) IoE eof ueof ⊢ errIsTerm eof ∗ errIsTerm ueof := by
  iintro #Henv
  iunfold decEnv at Henv
  icases Henv with ⟨#Hio, -, -, -, -, #Heof, #Hueof, -⟩
  ihave #Herrs : isPkgInit (PROP := IProp GF) pkg_id.errors $$ []
  · iPkgInit
  ihave #HI := io.isInit_access $$ Hio
  icases HI with ⟨-, -, -, -, #HE1, #HU1, -⟩
  iunfold errors.newVar at HE1
  icases HE1 with ⟨%x1, #Hx1, -⟩
  ihave ⟨%x2, #Hx2, -⟩ := errOk_newVar _ _ $$ HU1
  icombine Heof Hx1 gives %he
  icombine Hueof Hx2 gives %hu
  subst he hu
  isplitl []
  · iapply errIsTerm_errorString x1; iexact Herrs
  · iapply errIsTerm_errorString x2; iexact Herrs

/-- **`io.ErrUnexpectedEOF` is a pointer error** (`decEnv`'s `io` initialization): a target `errIsTerm`
admits. -/
theorem decEnv_ueof_ptr (IoE : GoInterface → Prop) (eof ueof : GoInterface) :
    decEnv (GF := GF) IoE eof ueof ⊢
      ⌜∀ tii, ueof = interface.ok tii → _root_.Perennial.errors.IsPointerError tii⌝ := by
  iintro #Henv
  iunfold decEnv at Henv
  icases Henv with ⟨#Hio, -, -, -, -, -, #Hueof, -⟩
  ihave #HI := io.isInit_access $$ Hio
  icases HI with ⟨-, -, -, -, -, #HU1, -⟩
  ihave ⟨%x2, #Hx2, -⟩ := errOk_newVar _ _ $$ HU1
  icombine Hueof Hx2 gives %hu
  ipureintro
  intro tii ht
  subst hu
  cases ht
  exact ⟨_, x2, rfl, rfl⟩

/-- **`io.EOF` is a target `fmt.ErrorfErrsNot.spec` admits** (`decEnv`'s `io` initialization): an `*errorString`, a
pointer error and no `*fmt.wrapError`. -/
theorem decEnv_eof_target (IoE : GoInterface → Prop) (eof ueof : GoInterface) :
    decEnv (GF := GF) IoE eof ueof ⊢
      ⌜∀ tii, eof = interface.ok tii → _root_.Perennial.errors.IsPointerError tii ∧
        tii.ty ≠ go.GoType.PointerType _root_.Perennial.fmt.wrapError.ty⌝ := by
  iintro #Henv
  iunfold decEnv at Henv
  icases Henv with ⟨#Hio, -, -, -, -, #Heof, -⟩
  ihave #HI := io.isInit_access $$ Hio
  icases HI with ⟨-, -, -, -, #HE1, -⟩
  iunfold errors.newVar at HE1
  icases HE1 with ⟨%x1, #Hx1, -⟩
  icombine Heof Hx1 gives %he
  ipureintro
  rw [he]
  exact errorString_target x1

/-- `decUe` of an error `errors.Is` returns on. -/
theorem decUe_term (e : GoInterface) : errIsTerm (GF := GF) e ⊢ decUe e := by
  iintro #H
  unfold decUe
  iright; ileft
  iexact H

/-- `decUe` of `nil`. -/
theorem decUe_nil : ⊢ decUe (GF := GF) GoInterface.nil := by
  unfold decUe
  ileft
  ipureintro
  rfl

/-- `decUe` of an I/O error (`notUeof`). -/
theorem decUe_not (e : GoInterface) : notUeof (GF := GF) e ⊢ decUe e := by
  iintro #H
  unfold decUe
  iright; iright
  iexact H

/-- `decUe` of `nil`, `io.EOF` or `io.ErrUnexpectedEOF`. -/
theorem decUe_eofOk (IoE : GoInterface → Prop) (eof ueof e : GoInterface)
    (h : e = GoInterface.nil ∨ e = eof ∨ e = ueof) :
    decEnv (GF := GF) IoE eof ueof ⊢ decUe e := by
  iintro #Henv
  ihave ⟨#H1, #H2⟩ := decEnv_term IoE eof ueof $$ Henv
  rcases h with rfl | rfl | rfl
  · iapply decUe_nil
  · iapply decUe_term; iexact H1
  · iapply decUe_term; iexact H2

/-- `decUe` of `nil`, `io.EOF` or `io.ErrUnexpectedEOF`, from their `errIsTerm`s. -/
theorem decUe_of_eq (eof ueof e : GoInterface) (h : e = GoInterface.nil ∨ e = eof ∨ e = ueof) :
    errIsTerm (GF := GF) eof ∗ errIsTerm ueof ⊢ decUe e := by
  iintro ⟨#H1, #H2⟩
  rcases h with rfl | rfl | rfl
  · iapply decUe_nil
  · iapply decUe_term; iexact H1
  · iapply decUe_term; iexact H2

/-- `decUe` of a reader's error (an I/O error with its `ioUeof`, or `nil`, `io.EOF`,
`io.ErrUnexpectedEOF`). -/
theorem decUe_rd (IoE : GoInterface → Prop) (eof ueof e : GoInterface)
    (h : IoE e ∨ e = GoInterface.nil ∨ e = eof ∨ e = ueof) :
    errIsTerm (GF := GF) eof ∗ errIsTerm ueof ∗ ioUeof IoE e ⊢ decUe e := by
  iintro ⟨#H1, #H2, #Hu⟩
  rcases h with hI | h
  · iunfold ioUeof at Hu
    icases Hu with (%hc | #Hn)
    · rcases hc with rfl | hc
      · iapply decUe_nil
      · exact absurd hI hc
    · iapply decUe_not; iexact Hn
  · iapply decUe_of_eq eof ueof e h
    iframe H1 H2

/-- **A `ReadFull`'s error is an I/O error, `nil`, `io.EOF` or `io.ErrUnexpectedEOF`.** -/
theorem rd_cases {bs r ys : List w8} {m : Nat} {eof ueof err : GoInterface} {IoE : GoInterface → Prop}
    (h : io.readFullOk (decRdErr bs eof IoE) eof ueof r ys m err) (hio : ¬ IoE eof) :
    IoE err ∨ err = GoInterface.nil ∨ err = eof ∨ err = ueof := by
  by_cases hn : err = GoInterface.nil
  · exact .inr (.inl hn)
  by_cases hI : IoE err
  · exact .inl hI
  obtain ⟨-, -, hc⟩ := readFull_short h hio hn hI
  rcases hc with ⟨h1, -⟩ | ⟨h1, -⟩
  · exact .inr (.inr (.inl h1))
  · exact .inr (.inr (.inr h1))

end term

end WalFs
end EtcdGrove
end Perennial

end

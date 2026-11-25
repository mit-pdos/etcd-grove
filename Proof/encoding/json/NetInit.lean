/-
What `net`'s initialization gives the encoding/json model's proofs on a connection: the value of
`poll.ErrDeadlineExceeded` (`ed_of_net`), which `net.Conn.Read.spec` and `Write.spec` name, and
`io.EOF`'s, an `*errorString` (`eof_of_net`), which `Decoder.fetch` compares a read's error with.
Lemmas over definitions only. Lean-first (no Rocq counterpart).
-/
module

public import Proof.internal.poll.PkgInit
public import Net.Proof.net.Base
public import Perennial.Proof.io.Base

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace encoding.json

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [HasExt netExt] [net.Assumptions]

/-- `poll.ErrDeadlineExceeded`'s value, from `net`'s initialization. -/
theorem ed_of_net :
    isPkgInit (PROP := IProp GF) pkg_id.net ⊢
      ∃ ed : GoInterface, globalAddr internal.poll.ErrDeadlineExceeded ↦□ ed := by
  iintro #Hnet
  ihave #Hpoll : (isPkgInit (PROP := IProp GF) pkg_id.internal.poll) $$ []
  · iPkgInit
  ihave #Hi := (isPkgInit_access (PROP := IProp GF) pkg_id.internal.poll) $$ Hpoll
  ihave #Hi2 : (iprop((∃ e : GoInterface, typedPointsto (globalAddr internal.poll.ErrNoDeadline) e DFrac.discard) ∗
    (∃ e : GoInterface, typedPointsto (globalAddr internal.poll.ErrDeadlineExceeded) e DFrac.discard) ∗
    (∃ x : Loc, typedPointsto (globalAddr internal.poll.ErrFileClosing)
      (interface.mkOk (go.GoType.PointerType _root_.Perennial.errors.errorString.ty) #x) DFrac.discard)) : IProp GF) $$ [Hi]
  · iexact Hi
  icases Hi2 with ⟨-, ⟨%ed, #Hed⟩, -⟩
  iexists ed
  iexact Hed

/-- `io.EOF`'s value, an `*errorString`, from `net`'s initialization. -/
theorem eof_of_net :
    isPkgInit (PROP := IProp GF) pkg_id.net ⊢
      ∃ x : Loc, globalAddr io.EOF ↦□
        interface.mkOk (go.GoType.PointerType _root_.Perennial.errors.errorString.ty) #x := by
  iintro #Hnet
  ihave #Hio : (isPkgInit (PROP := IProp GF) pkg_id.io) $$ []
  · iPkgInit
  ihave HEOF := _root_.Perennial.io.eof_of_init $$ Hio
  iunfold _root_.Perennial.errors.newVar at HEOF
  icases HEOF with ⟨%x, #HEOF, -⟩
  iexists x
  iexact HEOF

end lemmas

end encoding.json
end Perennial

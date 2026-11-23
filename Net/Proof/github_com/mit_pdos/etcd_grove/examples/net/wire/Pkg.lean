/-
The package facts the examples' proofs read (proved, not trusted): `poll.ErrDeadlineExceeded`'s
value, which `net.Conn.Read.spec`, `net.Conn.Write.spec` and `wire.ReadFull.spec` name (the `Err`
of a deadline's timeout), from `internal/poll`'s initialization (`poll_access`, `ed_of_poll`), or
from `wire`'s, which initializes `net` and so `internal/poll` (`ed_init`). An example's package
imports `wire`, so its own `isPkgInit` gives `wire`'s (`iPkgInit`).
-/
module

public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.wire.Base

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace github_com.mit_pdos.etcd_grove.examples.net.wire

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `internal/poll`'s package fact (the main tree's, `Proof/internal/poll/PkgInit.lean`), its first two
conjuncts (the third, `ErrFileClosing` an `*errorString`, unused here). -/
theorem poll_access :
    isPkgInit (PROP := IProp GF) pkg_id.internal.poll ⊢
      iprop((∃ e : GoInterface, globalAddr internal.poll.ErrNoDeadline ↦□ e) ∗
        (∃ e : GoInterface, globalAddr internal.poll.ErrDeadlineExceeded ↦□ e)) := by
  refine (isPkgInit_access (PROP := IProp GF) pkg_id.internal.poll).trans ?_
  show iprop((∃ e : GoInterface, typedPointsto (globalAddr internal.poll.ErrNoDeadline) e DFrac.discard) ∗
    (∃ e : GoInterface, typedPointsto (globalAddr internal.poll.ErrDeadlineExceeded) e DFrac.discard) ∗
    (∃ x : Loc, typedPointsto (globalAddr internal.poll.ErrFileClosing)
      (interface.mkOk (go.GoType.PointerType _root_.Perennial.errors.errorString.ty) #x) DFrac.discard)) ⊢ _
  iintro ⟨#Hn, #Hd, -⟩
  isplitl [Hn]
  · iexact Hn
  · iexact Hd

/-- `poll.ErrDeadlineExceeded`'s value, from `internal/poll`'s initialization. -/
theorem ed_of_poll :
    isPkgInit (PROP := IProp GF) pkg_id.internal.poll ⊢
      ∃ ed : GoInterface, globalAddr internal.poll.ErrDeadlineExceeded ↦□ ed := by
  iintro #Hpoll
  ihave #Hi := poll_access $$ Hpoll
  icases Hi with ⟨-, %ed, #Hed⟩
  iexists ed
  iexact Hed

/-- `poll.ErrDeadlineExceeded`'s value, from `wire`'s initialization. -/
theorem ed_init :
    isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.net.wire ⊢
      ∃ ed : GoInterface, globalAddr internal.poll.ErrDeadlineExceeded ↦□ ed := by
  iintro #Hpkg
  ihave #Hpoll : (isPkgInit (PROP := IProp GF) pkg_id.internal.poll) $$ []
  · iPkgInit
  iapply ed_of_poll $$ Hpoll

end proof

end github_com.mit_pdos.etcd_grove.examples.net.wire
end Perennial

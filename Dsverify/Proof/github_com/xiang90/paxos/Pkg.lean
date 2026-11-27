/-
The package facts the transport's proofs read (proved, not trusted), from paxos's initialization,
which initializes `net`, `io` and `internal/poll` (`iPkgInit`): `io.EOF`'s value (`eof_init`),
`poll.ErrDeadlineExceeded`'s (`ed_init`) and `net`'s `errTimeout` (`et_init`), which the net specs
name. (As `examples/lib/remote`'s `Pkg.lean`.)
-/
module

public import Dsverify.Proof.github_com.xiang90.paxos.Base
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.wire.Pkg
public import Perennial.Proof.io.Base

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace github_com.xiang90.paxos

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : net.Assumptions]

/-- `io.EOF`'s value. -/
theorem eof_init :
    isPkgInit (PROP := IProp GF) pkg_id.github_com.xiang90.paxos ⊢
      ∃ eof : GoInterface, globalAddr io.EOF ↦□ eof := by
  iintro #Hpkg
  ihave #Hio : (isPkgInit (PROP := IProp GF) pkg_id.io) $$ []
  · iPkgInit
  ihave #Hn := io.eof_of_init $$ Hio
  isimp only [_root_.Perennial.errors.newVar] at Hn
  icases Hn with ⟨%eofl, #Heof, -⟩
  iexists _
  iexact Heof

/-- `poll.ErrDeadlineExceeded`'s value. -/
theorem ed_init :
    isPkgInit (PROP := IProp GF) pkg_id.github_com.xiang90.paxos ⊢
      ∃ ed : GoInterface, globalAddr internal.poll.ErrDeadlineExceeded ↦□ ed := by
  iintro #Hpkg
  ihave #Hpoll : (isPkgInit (PROP := IProp GF) pkg_id.internal.poll) $$ []
  · iPkgInit
  iapply github_com.mit_pdos.etcd_grove.examples.net.wire.ed_of_poll $$ Hpoll

/-- `net`'s `errTimeout`'s value. -/
theorem et_init :
    isPkgInit (PROP := IProp GF) pkg_id.github_com.xiang90.paxos ⊢
      ∃ et : GoInterface, globalAddr net.errTimeout ↦□ et := by
  iintro #Hpkg
  ihave #Hnet : (isPkgInit (PROP := IProp GF) pkg_id.net) $$ []
  · iPkgInit
  ihave #Hi : net.isInit $$ []
  · with_unfolding_all iapply isPkgInit_access (PROP := IProp GF) pkg_id.net $$ Hnet
  icases Hi with ⟨-, -, %p, #Ht⟩
  iexists _
  iexact Ht

end proof

end github_com.xiang90.paxos
end Perennial

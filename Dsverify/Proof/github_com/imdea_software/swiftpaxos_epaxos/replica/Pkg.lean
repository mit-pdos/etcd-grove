/-
The package facts the replica's network proofs read, from `replica`'s initialization (which
initializes `io`, `net` and so `internal/poll`; `iPkgInit`): `io.EOF`'s value and
`poll.ErrDeadlineExceeded`'s, which `Net/`'s connection contracts name (as paxos's `Pkg.lean`).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.replica.Specs
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.wire.Pkg
public import Perennial.Proof.io.Base

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net

section heap
variable [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [go.Semantics]
variable [epaxos.Assumptions] [HasExt netExt]

/-- `io.EOF`'s and `poll.ErrDeadlineExceeded`'s values. -/
theorem replica_net_errs :
    isPkgInit (PROP := IProp GF) pkg_id.github_com.imdea_software.swiftpaxos_epaxos.replica ⊢
      ∃ eof ed : GoInterface, globalAddr io.EOF ↦□ eof ∗
        globalAddr internal.poll.ErrDeadlineExceeded ↦□ ed := by
  iintro #Hpkg
  ihave #Hio : (isPkgInit (PROP := IProp GF) pkg_id.io) $$ []
  · iPkgInit
  ihave #Hn := io.eof_of_init $$ Hio
  isimp only [_root_.Perennial.errors.newVar] at Hn
  icases Hn with ⟨%eofl, #Heof, -⟩
  ihave #Hpoll : (isPkgInit (PROP := IProp GF) pkg_id.internal.poll) $$ []
  · iPkgInit
  ihave ⟨%ed, #Hed⟩ := github_com.mit_pdos.etcd_grove.examples.net.wire.ed_of_poll $$ Hpoll
  iexists _, ed
  iframe Heof Hed

end heap

end Perennial.github_com.imdea_software.swiftpaxos_epaxos

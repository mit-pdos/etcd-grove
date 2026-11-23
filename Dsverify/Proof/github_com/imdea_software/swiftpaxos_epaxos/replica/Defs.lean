/-
`replica/defs` helpers the framework calls (package-internal specs, the cases the run uses):
the latency table's waits on a nil table (`r.Dt` is nil: no latency file).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.replica.Specs

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net github_com.imdea_software.swiftpaxos_epaxos.kvs model

attribute [local instance] GooseGlobalGS.gooseInvGS

section heap
variable [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [go.Semantics]
variable [epaxos.Assumptions] [HasExt netExt] [π : NetProtoGS]

/-- `dt.WaitDurationID(i)` on a nil table: 0. -/
theorem wp_WaitDurationID_nil (i : w64) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.imdea_software.swiftpaxos_epaxos.replica.defs }}
      (App (Val ((null : Loc) @!! go.GoType.PointerType replica.defs.LatencyTable.ty @!!
        go!"WaitDurationID")) (Val #i))
    {{ RET #(W64 0); True }} := by
  wp_start
  wp_auto
  wp_end

/-- `dt.WaitDuration(a)` on a nil table: 0. -/
theorem wp_WaitDuration_nil (a : GoString) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.imdea_software.swiftpaxos_epaxos.replica.defs }}
      (App (Val ((null : Loc) @!! go.GoType.PointerType replica.defs.LatencyTable.ty @!!
        go!"WaitDuration")) (Val #a))
    {{ RET #(W64 0); True }} := by
  wp_start
  wp_auto
  wp_end

end heap

end Perennial.github_com.imdea_software.swiftpaxos_epaxos

/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/appendStats.lean (241f27e).
-/
/-
`raft.appendStats`'s spec (replication subsystem, internal).
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.ReplBase

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std
open github_com.hashicorp.raft github_com.hashicorp.raft.gprot github_com.hashicorp.raft.proto

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.Assumptions]

/-- `appendStats`: no effect (the metrics calls are not in the translated code). -/
abbrev github_com.hashicorp.raft.appendStats.spec : Prop :=
  ∀ (peer : GoString) (start : time.Time) (logs : w64) (skip : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft }}
    (App (App (App (App (Val (@! github_com.hashicorp.raft.appendStats)) (Val #peer)) (Val #start))
      (Val #logs)) (Val #skip))
  {{ RET #(); True }}

end spec

end Perennial

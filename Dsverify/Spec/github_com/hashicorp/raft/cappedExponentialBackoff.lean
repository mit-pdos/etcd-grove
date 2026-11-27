/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/cappedExponentialBackoff.lean (241f27e).
-/
/-
`raft.cappedExponentialBackoff`'s spec (raft-internal interface, notes/raft-iface.md). Arithmetic on durations (no panic).
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.core.Laws

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

/-- `cappedExponentialBackoff`: Arithmetic on durations (no panic). -/
abbrev github_com.hashicorp.raft.cappedExponentialBackoff.spec : Prop :=
  ∀ (base : time.Duration) (round limit : w64) (cap : time.Duration),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft }}
    (App (App (App (App (Val (@! github_com.hashicorp.raft.cappedExponentialBackoff)) (Val #base)) (Val #round)) (Val #limit)) (Val #cap))
  {{ (d : time.Duration), RET #d; True }}

end spec

end Perennial

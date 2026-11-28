/-
(hraft_robust R3) The spec of `disk.copyBytes` (`disk.go`).
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.disk.Codec

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.examples.hraftnet.disk.Assumptions]

open github_com.hashicorp.raft.examples.hraftnet.disk in
/-- `copyBytes(b)`: a fresh copy of the bytes of `b`. -/
abbrev github_com.hashicorp.raft.examples.hraftnet.disk.copyBytes.spec : Prop :=
  ∀ (b : GoSlice) (dq : DFrac) (bs : List w8),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.hraftnet.disk ∗ b ↦*{dq} bs }}
    (App (Val (@! github_com.hashicorp.raft.examples.hraftnet.disk.copyBytes)) (Val #b))
  {{ (c : GoSlice), RET #c; b ↦*{dq} bs ∗ c ↦* bs }}

end spec

end Perennial

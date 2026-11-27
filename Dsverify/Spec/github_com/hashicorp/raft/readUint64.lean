/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/readUint64.lean (241f27e).
-/
/-
`raft.readUint64`'s spec (API-internal, encoding.go): the success case.
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

/-- `readUint64(b)` on bytes starting with the encoding of `x`: returns `x`, the rest of the
slice (with a way back to the whole slice), and nil. -/
abbrev github_com.hashicorp.raft.readUint64.spec : Prop :=
  ∀ (b : GoSlice) (x : w64) (rest : List w8) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ b ↦*{dq} (le64 x ++ rest) }}
    (App (Val (@! github_com.hashicorp.raft.readUint64)) (Val #b))
  {{ (b' : GoSlice), RET (PairV (PairV #x #b') #interface.nil); b' ↦*{dq} rest ∗
      (b' ↦*{dq} rest -∗ b ↦*{dq} (le64 x ++ rest)) }}

end spec

end Perennial

/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/readBytes.lean (241f27e).
-/
/-
`raft.readBytes`'s spec (API-internal, encoding.go): the success case.
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

/-- `readBytes(b)` on bytes starting with a length-prefixed `xs`: returns a fresh copy of `xs`,
the rest of the slice (with a way back to the whole slice), and nil. -/
abbrev github_com.hashicorp.raft.readBytes.spec : Prop :=
  ∀ (b : GoSlice) (xs rest : List w8) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗
     b ↦*{dq} (le64 (W64 xs.length) ++ xs ++ rest) }}
    (App (Val (@! github_com.hashicorp.raft.readBytes)) (Val #b))
  {{ (out b' : GoSlice), RET (PairV (PairV #out #b') #interface.nil); out ↦* xs ∗ b' ↦*{dq} rest ∗
      (b' ↦*{dq} rest -∗ b ↦*{dq} (le64 (W64 xs.length) ++ xs ++ rest)) }}

end spec

end Perennial

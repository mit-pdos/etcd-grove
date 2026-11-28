/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/appendBytes.lean (241f27e).
-/
/-
`raft.appendBytes`'s spec (API-internal, encoding.go).
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

/-- `appendBytes(b, s)`: appends the length of `s` (8 bytes) and `s`. -/
abbrev github_com.hashicorp.raft.appendBytes.spec : Prop :=
  ∀ (b : GoSlice) (bs : List w8) (s : GoSlice) (xs : List w8) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ b ↦* bs ∗
     ownSliceCap w8 b (DFrac.own 1) ∗ s ↦*{dq} xs }}
    (App (App (Val (@! github_com.hashicorp.raft.appendBytes)) (Val #b)) (Val #s))
  {{ (b' : GoSlice), RET #b'; b' ↦* (bs ++ le64 (W64 xs.length) ++ xs) ∗
      ownSliceCap w8 b' (DFrac.own 1) ∗ s ↦*{dq} xs }}

end spec

end Perennial

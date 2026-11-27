/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/appendUint64.lean (241f27e).
-/
/-
`raft.appendUint64`'s spec (API-internal, encoding.go).
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

/-- `appendUint64(b, x)`: appends the 8 little-endian bytes of `x`. -/
abbrev github_com.hashicorp.raft.appendUint64.spec : Prop :=
  ∀ (b : GoSlice) (bs : List w8) (x : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ b ↦* bs ∗
     ownSliceCap w8 b (DFrac.own 1) }}
    (App (App (Val (@! github_com.hashicorp.raft.appendUint64)) (Val #b)) (Val #x))
  {{ (b' : GoSlice), RET #b'; b' ↦* (bs ++ le64 x) ∗ ownSliceCap w8 b' (DFrac.own 1) }}

end spec

end Perennial

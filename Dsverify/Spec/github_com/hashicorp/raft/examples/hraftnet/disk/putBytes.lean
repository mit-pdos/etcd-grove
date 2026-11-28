/-
(hraft_robust R3) The spec of `disk.putBytes` (`codec.go`).
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.disk.Codec

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.examples.hraftnet.disk.Assumptions]

open github_com.hashicorp.raft.examples.hraftnet.disk in
/-- `putBytes(b, s)` appends `s`'s length (`encU64`) and its bytes (`encBytes`). -/
abbrev github_com.hashicorp.raft.examples.hraftnet.disk.putBytes.spec : Prop :=
  ∀ (b s : GoSlice) (bs cs : List w8) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.hraftnet.disk ∗
      b ↦* bs ∗ ownSliceCap w8 b (DFrac.own 1) ∗ s ↦*{dq} cs }}
    (App (App (Val (@! github_com.hashicorp.raft.examples.hraftnet.disk.putBytes)) (Val #b)) (Val #s))
  {{ (b' : GoSlice), RET #b'; b' ↦* (bs ++ encBytes cs) ∗ ownSliceCap w8 b' (DFrac.own 1) ∗ s ↦*{dq} cs }}

end spec

end Perennial

/-
(hraft_robust R3) The spec of `disk.putUint64` (`codec.go`).
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
/-- `putUint64(b, x)` appends `x`'s eight bytes, little-endian (`encU64`). -/
abbrev github_com.hashicorp.raft.examples.hraftnet.disk.putUint64.spec : Prop :=
  ∀ (b : GoSlice) (bs : List w8) (x : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.hraftnet.disk ∗
      b ↦* bs ∗ ownSliceCap w8 b (DFrac.own 1) }}
    (App (App (Val (@! github_com.hashicorp.raft.examples.hraftnet.disk.putUint64)) (Val #b)) (Val #x))
  {{ (b' : GoSlice), RET #b'; b' ↦* (bs ++ encU64 x) ∗ ownSliceCap w8 b' (DFrac.own 1) }}

end spec

end Perennial

/-
(hraft_robust R3) The spec of `disk.encodeConfiguration` (`snap.go`).
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.disk.Defs

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

open github_com.hashicorp.raft github_com.hashicorp.raft.examples.hraftnet.disk in
/-- `encodeConfiguration(b, c)` appends the encoding of `c`'s servers (`encCfg`). -/
abbrev github_com.hashicorp.raft.examples.hraftnet.disk.encodeConfiguration.spec : Prop :=
  ∀ (b : GoSlice) (bs : List w8) (c : Configuration) (ss : List SServer),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.hraftnet.disk ∗
      b ↦* bs ∗ ownSliceCap w8 b (DFrac.own 1) ∗ cfgRep c ss }}
    (App (App (Val (@! github_com.hashicorp.raft.examples.hraftnet.disk.encodeConfiguration)) (Val #b)) (Val #c))
  {{ (b' : GoSlice), RET #b'; b' ↦* (bs ++ encCfg ss) ∗ ownSliceCap w8 b' (DFrac.own 1) }}

end spec

end Perennial

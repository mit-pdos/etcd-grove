/-
`hraftnet.opID`'s spec (the hraft kit, notes/dsv-hraft.md, S5f).
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.ClientDefs

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.examples.hraftnet.Assumptions]

open github_com.hashicorp.raft.examples.hraftnet

/-- `opID(c, seq)`: a fresh slice of the eight bytes, big-endian, of `c << 56 | seq % 2^56`
(`opIDB`). -/
abbrev github_com.hashicorp.raft.examples.hraftnet.opID.spec : Prop :=
  ∀ (c s : w64),
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.hraftnet }}
      (App (App (Val (@! opID)) (Val #c)) (Val #s))
    {{ (sl : GoSlice), RET #sl; sl ↦* opIDB c s ∗ ownSliceCap w8 sl (DFrac.own 1) }}

end spec

end Perennial

/-
`rpctransport.BytesBound`'s spec (the hraft kit's transport, notes/dsv-hraft.md, S4).
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.rpctransport.Wire

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.examples.hraftnet.rpctransport.Assumptions]

open github_com.hashicorp.raft.examples.hraftnet.rpctransport

/-- `BytesBound(b)`: the bound of a byte-slice field of `bs.length` bytes (`bytesBoundN`). -/
abbrev github_com.hashicorp.raft.examples.hraftnet.rpctransport.BytesBound.spec : Prop :=
  ∀ (b : GoSlice) (dq : DFrac) (bs : List w8),
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.hraftnet.rpctransport ∗
        b ↦*{dq} bs }}
      (App (Val (@! BytesBound)) (Val #b))
    {{ (r : w64), RET #r; ⌜uint.nat r = bytesBoundN bs.length⌝ ∗ b ↦*{dq} bs }}

end spec

end Perennial

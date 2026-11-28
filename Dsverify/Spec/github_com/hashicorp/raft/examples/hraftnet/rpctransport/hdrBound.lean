/-
`rpctransport.hdrBound`'s spec (the hraft kit's transport, notes/dsv-hraft.md, S4).
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

/-- `hdrBound(h)`: the bound of a `Header` field (`hdrBoundN`). -/
abbrev github_com.hashicorp.raft.examples.hraftnet.rpctransport.hdrBound.spec : Prop :=
  ∀ (h : Loc) (dq : DFrac) (hv : Header) (dq1 dq2 : DFrac) (id ad : List w8),
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.hraftnet.rpctransport ∗
        h ↦{dq} hv ∗ hv.ID' ↦*{dq1} id ∗ hv.Addr' ↦*{dq2} ad }}
      (App (Val (@! hdrBound)) (Val #h))
    {{ (r : w64), RET #r; ⌜uint.nat r = hdrBoundN id ad⌝ ∗
        h ↦{dq} hv ∗ hv.ID' ↦*{dq1} id ∗ hv.Addr' ↦*{dq2} ad }}

end spec

end Perennial

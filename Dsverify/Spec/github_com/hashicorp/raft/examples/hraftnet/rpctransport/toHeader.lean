/-
`rpctransport.toHeader`'s spec (the hraft kit's transport, notes/dsv-hraft.md, S4).
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

/-- `toHeader(h)`: the wire header of raft's `h`, with fresh byte slices. -/
abbrev github_com.hashicorp.raft.examples.hraftnet.rpctransport.toHeader.spec : Prop :=
  ∀ (h : github_com.hashicorp.raft.RPCHeader) (dq1 dq2 : DFrac) (id ad : List w8),
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.hraftnet.rpctransport ∗
        h.ID' ↦*{dq1} id ∗ h.Addr' ↦*{dq2} ad }}
      (App (Val (@! toHeader)) (Val #h))
    {{ (i a : GoSlice), RET #(Header.mk h.ProtocolVersion' i a);
        h.ID' ↦*{dq1} id ∗ h.Addr' ↦*{dq2} ad ∗ i ↦* id ∗ a ↦* ad }}

end spec

end Perennial

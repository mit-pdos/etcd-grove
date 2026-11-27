/-
`rpctransport.AppendReqBound`'s spec (the hraft kit's transport, notes/dsv-hraft.md, S4).
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

/-- `AppendReqBound(a)`: `aeBoundN` of the request's header slices, leader and entries. -/
abbrev github_com.hashicorp.raft.examples.hraftnet.rpctransport.AppendReqBound.spec : Prop :=
  ∀ (a : Loc) (dq : DFrac) (w : AppendReq) (dq1 : DFrac) (id ad ld : List w8) (vs : List EntV),
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.hraftnet.rpctransport ∗
        a ↦{dq} w ∗ w.Hdr'.ID' ↦*{dq1} id ∗ w.Hdr'.Addr' ↦*{dq1} ad ∗ w.Leader' ↦*{dq1} ld ∗
        entsOwn w.Entries' dq1 vs }}
      (App (Val (@! AppendReqBound)) (Val #a))
    {{ (r : w64), RET #r; ⌜uint.nat r = aeBoundN id ad ld vs⌝ ∗
        a ↦{dq} w ∗ w.Hdr'.ID' ↦*{dq1} id ∗ w.Hdr'.Addr' ↦*{dq1} ad ∗ w.Leader' ↦*{dq1} ld ∗
        entsOwn w.Entries' dq1 vs }}

end spec

end Perennial

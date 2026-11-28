/-
`rpctransport.pipeline.Consumer`'s spec (the hraft kit's transport, notes/dsv-hraft.md, S4).
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.rpctransport.Trans

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
variable [π : Net.NetProtoGS] [net.rpc.Assumptions] [net.Assumptions]

open github_com.hashicorp.raft.examples.hraftnet.rpctransport

/-- `p.Consumer()`: the futures' channel. -/
abbrev github_com.hashicorp.raft.examples.hraftnet.rpctransport.pipeline.Consumer.spec : Prop :=
  ∀ (p : Loc) (γ : github_com.hashicorp.raft.gprot.GNames) (j : github_com.hashicorp.raft.proto.SID) (T : Nat),
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.hraftnet.rpctransport ∗ isPip p γ j T }}
      (App (Val (p @!! go.GoType.PointerType pipeline.ty @!! go!"Consumer")) (Val #()))
    {{ (ch : Loc), RET #ch; ∃ γc : ChanNames, isChanBag (V := GoInterface) γc ch (github_com.hashicorp.raft.pipeFut γ j T) }}

end spec

end Perennial

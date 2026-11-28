/-
`rpctransport.pipeline.AppendEntries`'s spec (the hraft kit's transport, notes/dsv-hraft.md, S4).
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

/-- `p.AppendEntries(args, resp)`: queues a future of the valid request of term `T` (read-only from now on) and the lent response struct; an error once the pipeline is closed. -/
abbrev github_com.hashicorp.raft.examples.hraftnet.rpctransport.pipeline.AppendEntries.spec : Prop :=
  ∀ (p : Loc) (γ : github_com.hashicorp.raft.gprot.GNames) (j : github_com.hashicorp.raft.proto.SID) (T : Nat) (args resp : Loc)
    (rq : github_com.hashicorp.raft.AppendEntriesRequest) (rp0 : github_com.hashicorp.raft.AppendEntriesResponse)
    (snd : github_com.hashicorp.raft.proto.SID) (prev pt : Nat) (ents : github_com.hashicorp.raft.proto.RLog) (lci : Nat) (ss : github_com.hashicorp.raft.proto.Snap),
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.hraftnet.rpctransport ∗ isPip p γ j T ∗
        args ↦□ rq ∗ github_com.hashicorp.raft.aeReq γ rq snd T prev pt ents lci ss ∗ resp ↦ rp0 ∗ ⌜rp0.Success' = false⌝ }}
      (App (App (Val (p @!! go.GoType.PointerType pipeline.ty @!! go!"AppendEntries")) (Val #args)) (Val #resp))
    {{ (fi err : GoInterface), RET (PairV #fi #err); ⌜err = interface.nil⌝ ∨ github_com.hashicorp.raft.errOk err }}

end spec

end Perennial

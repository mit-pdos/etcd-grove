/-
`rpctransport.RaftRPC.AppendEntries`'s spec (the hraft kit's transport, notes/dsv-hraft.md, S4).
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

/-- `s.AppendEntries(args, reply)`: the request decoded into `args` (valid, `aeReqW`) handed to raft (`deliver`, a heartbeat to its handler); `reply` its answer with the responder's facts, or the failure. -/
abbrev github_com.hashicorp.raft.examples.hraftnet.rpctransport.RaftRPC.AppendEntries.spec : Prop :=
  ∀ (s : Loc) (γ : github_com.hashicorp.raft.gprot.GNames) (snapP : Nat → List w8 → IProp GF) (i : github_com.hashicorp.raft.proto.SID) (W : net.rpc.RpcWorld GF)
    (C : net.rpc.CodecSpec GF) (args reply : Loc) (w : AppendReq) (v : AEReqV) (snd : github_com.hashicorp.raft.proto.SID) (T prev pt : Nat) (ents : github_com.hashicorp.raft.proto.RLog) (lci : Nat) (ss : github_com.hashicorp.raft.proto.Snap),
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.hraftnet.rpctransport ∗ isRcv s γ snapP i W C ∗ args ↦ w ∗ aeReqOwn w (DFrac.own 1) v ∗ aeReqW γ v snd T prev pt ents lci ss ∗
        reply ↦ (zeroValDef : AppendResp) }}
      (App (App (Val (s @!! go.GoType.PointerType RaftRPC.ty @!! go!"AppendEntries")) (Val #args)) (Val #reply))
    {{ RET #interface.nil; ∃ (w' : AppendResp) (r : AERespV), reply ↦ w' ∗ aeRespOwn w' (DFrac.own 1) r ∗ aeRespW γ r i T (prev + ents.length) (github_com.hashicorp.raft.isHb prev ents lci) ss }}

end spec

end Perennial

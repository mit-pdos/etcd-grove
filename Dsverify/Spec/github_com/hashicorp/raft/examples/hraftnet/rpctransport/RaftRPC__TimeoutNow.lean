/-
`rpctransport.RaftRPC.TimeoutNow`'s spec (the hraft kit's transport, notes/dsv-hraft.md, S4).
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

/-- `s.TimeoutNow(args, reply)`: as `AppendEntries`, for a TimeoutNow request. -/
abbrev github_com.hashicorp.raft.examples.hraftnet.rpctransport.RaftRPC.TimeoutNow.spec : Prop :=
  ∀ (s : Loc) (γ : github_com.hashicorp.raft.gprot.GNames) (snapP : Nat → List w8 → IProp GF) (i : github_com.hashicorp.raft.proto.SID) (W : net.rpc.RpcWorld GF)
    (C : net.rpc.CodecSpec GF) (args reply : Loc) (w : TimeoutReq) (h : HdrV) (c : github_com.hashicorp.raft.proto.SID),
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.hraftnet.rpctransport ∗ isRcv s γ snapP i W C ∗ args ↦ w ∗ hdrOwn w.Hdr' (DFrac.own 1) h ∗ ⌜tnReqW h c⌝ ∗
        reply ↦ (zeroValDef : TimeoutResp) }}
      (App (App (Val (s @!! go.GoType.PointerType RaftRPC.ty @!! go!"TimeoutNow")) (Val #args)) (Val #reply))
    {{ RET #interface.nil; ∃ (w' : TimeoutResp) (r : TimeoutRespV), reply ↦ w' ∗ timeoutRespOwn w' (DFrac.own 1) r }}

end spec

end Perennial

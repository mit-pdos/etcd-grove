/-
`rpctransport.Transport.InstallSnapshot`'s spec (the hraft kit's transport, notes/dsv-hraft.md, S4).
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

/-- `t.InstallSnapshot(id, j, args, resp, data)`: the snapshot read from `data` in full and sent with the valid request to `j`; `j`'s response, or an error. -/
abbrev github_com.hashicorp.raft.examples.hraftnet.rpctransport.Transport.InstallSnapshot.spec : Prop :=
  ∀ (t : Loc) (γ : github_com.hashicorp.raft.gprot.GNames) (snapP : Nat → List w8 → IProp GF) (i : github_com.hashicorp.raft.proto.SID) (W : net.rpc.RpcWorld GF) (C : net.rpc.CodecSpec GF) (id : GoString) (j : github_com.hashicorp.raft.proto.SID) (args resp : Loc) (rq : github_com.hashicorp.raft.InstallSnapshotRequest) (rp0 : github_com.hashicorp.raft.InstallSnapshotResponse) (dq : DFrac)
    (snd : github_com.hashicorp.raft.proto.SID) (T s st : Nat) (b : List w8) (data : GoInterfaceOk),
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.hraftnet.rpctransport ∗ isTrans t γ snapP i W C ∗ args ↦{dq} rq ∗ github_com.hashicorp.raft.isReq γ rq snd j T s st b ∗ resp ↦ rp0 ∗ github_com.hashicorp.raft.snapStream data snapP s b }}
      (App (App (App (App (App (Val (t @!! go.GoType.PointerType Transport.ty @!! go!"InstallSnapshot")) (Val #id)) (Val #(j : GoString))) (Val #args)) (Val #resp)) (Val #(GoInterface.ok data)))
    {{ (err : GoInterface), RET #err; args ↦{dq} rq ∗
        ((⌜err = interface.nil⌝ ∗ ∃ rp : github_com.hashicorp.raft.InstallSnapshotResponse, resp ↦ rp ∗ github_com.hashicorp.raft.isResp γ rp) ∨
         (errStr err ∗ resp ↦ rp0)) }}

end spec

end Perennial

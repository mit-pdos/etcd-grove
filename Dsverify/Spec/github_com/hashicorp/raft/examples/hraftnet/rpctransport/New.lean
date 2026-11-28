/-
`rpctransport.New`'s spec (the hraft kit's transport, notes/dsv-hraft.md, S4).
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

/-- `New(local, peers, timeout)`: server `local`'s transport, its peers `peers[a]` for each raft address `a`: each a net/rpc server of the world `W` whose `RaftRPC` service is `a`'s (`raftSvc`), with the registered codec `C` meeting the sender's laws. -/
abbrev github_com.hashicorp.raft.examples.hraftnet.rpctransport.New.spec : Prop :=
  ∀ (lc : GoString) (peers : Loc) (dq : DFrac) (M : GMap GoString GoString) (d : w64) (γ : github_com.hashicorp.raft.gprot.GNames)
    (snapP : Nat → List w8 → IProp GF) (W : net.rpc.RpcWorld GF) (C : net.rpc.CodecSpec GF),
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.hraftnet.rpctransport ∗ peers ↦${dq} M ∗
        ([∗map] a ↦ na ∈ M, net.rpc.rpcAddr (Gg := hG.goose_globalGS) W na ∗ ⌜W.SS na svcName = some (raftSvc γ snapP a)⌝) ∗
        ⌜receiptBound GF ≤ 2 ^ 64⌝ ∗ net.rpc.codecSet C ∗ ⌜CodecLaws C⌝ }}
      (App (App (App (Val (@! New)) (Val #lc)) (Val #peers)) (Val #d))
    {{ (t : Loc), RET #t; peers ↦${dq} M ∗ isTrans t γ snapP lc W C }}

end spec

end Perennial

/-
`rpctransport.Transport.send`'s spec (the hraft kit's transport, notes/dsv-hraft.md, S4).
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

/-- `t.send(j, M, req, reply)`: `RaftRPC.M` at `j`'s peer (`Conn.Call` with the transport's timeout): `nil` with the decoded answer (`Θ rep true`) after one run of `j`'s method on the deposit, or an `errors.New` error (`j` no peer, or no answer). -/
abbrev github_com.hashicorp.raft.examples.hraftnet.rpctransport.Transport.send.spec : Prop :=
  ∀ (t : Loc) (γ : github_com.hashicorp.raft.gprot.GNames) (snapP : Nat → List w8 → IProp GF) (i : github_com.hashicorp.raft.proto.SID) (W : net.rpc.RpcWorld GF) (C : net.rpc.CodecSpec GF) (j M : GoString) (req reply : GoInterface)
    (Φm : List w8 → GoString → IProp GF) (Rargs D : IProp GF) (Θ : List w8 → Bool → IProp GF),
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.hraftnet.rpctransport ∗ isTrans t γ snapP i W C ∗
        ⌜net.rpc.splitSM (svcName ++ go!"." ++ M) = some (svcName, M) ∧
          (svcName ++ go!"." ++ M).length + 16 ≤ net.rpc.maxFrameN ∧ reply ≠ interface.nil⌝ ∗
        C.enc req (fun bs => iprop(⌜bs.length ≤ net.rpc.maxFrameN⌝ ∗ raftSvc γ snapP j M bs Φm ∗ Rargs)) ∗ D ∗
        □ (D -∗ ∀ rep, Φm rep [] -∗ C.dec rep reply (Θ rep)) }}
      (App (App (App (App (Val (t @!! go.GoType.PointerType Transport.ty @!! go!"send")) (Val #j)) (Val #M)) (Val #req)) (Val #reply))
    {{ (err : GoInterface), RET #err; (⌜err = interface.nil⌝ ∗ ∃ rep, Θ rep true) ∨ errStr err }}

end spec

end Perennial

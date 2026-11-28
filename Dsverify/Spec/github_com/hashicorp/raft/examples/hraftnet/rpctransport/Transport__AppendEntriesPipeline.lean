/-
`rpctransport.Transport.AppendEntriesPipeline`'s spec (the hraft kit's transport, notes/dsv-hraft.md, S4).
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

/-- `t.AppendEntriesPipeline(id, j)`: a pipeline to `j` (of the replication goroutine's term `T`, a ghost parameter). -/
abbrev github_com.hashicorp.raft.examples.hraftnet.rpctransport.Transport.AppendEntriesPipeline.spec : Prop :=
  ∀ (t : Loc) (γ : github_com.hashicorp.raft.gprot.GNames) (snapP : Nat → List w8 → IProp GF) (i : github_com.hashicorp.raft.proto.SID) (W : net.rpc.RpcWorld GF) (C : net.rpc.CodecSpec GF) (id : GoString) (j : github_com.hashicorp.raft.proto.SID) (T : Nat),
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.hraftnet.rpctransport ∗ isTrans t γ snapP i W C }}
      (App (App (Val (t @!! go.GoType.PointerType Transport.ty @!! go!"AppendEntriesPipeline")) (Val #id)) (Val #(j : GoString)))
    {{ (p err : GoInterface), RET (PairV #p #err); ⌜err = interface.nil⌝ ∗
        ∃ pI : GoInterfaceOk, ⌜p = GoInterface.ok pI⌝ ∗ github_com.hashicorp.raft.isPipeline pI γ j T }}

end spec

end Perennial

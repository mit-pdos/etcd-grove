/-
The definitions, specs and lemmas of `Methods.lean` that its proofs do not need (split out for the import tiers, CLAUDE.md "Import tiers": its importers that are not linking modules import this module, and see no proof).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.master.Defs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section spec
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF]
variable [master.Assumptions]

/-- `m.GetReplicaList(args, reply)`: blocks until `run` has finished its initialization (the
membership is then fixed), and answers it, `Ready`, with one alive flag per replica. -/
abbrev master.Master.GetReplicaList.spec : Prop :=
  ∀ (m : Loc) (γc γm : GName) (N : Nat) (args reply : Loc)
    (rv : replica.defs.GetReplicaListReply),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.master ∗
      master.isMaster m γc γm N ∗ reply ↦ rv }}
    (App (App (Val (m @!! go.GoType.PointerType master.Master.ty @!! go!"GetReplicaList"))
      (Val #args)) (Val #reply))
  {{ RET #(interface.nil : GoInterface);
      ∃ (s1 s2 : GoSlice) (nodes : List GoString) (alive : List Bool),
        reply ↦ replica.defs.GetReplicaListReply.mk s1 s2 true ∗ s1 ↦* nodes ∗ s2 ↦* alive ∗
        (∃ fr, sp.cfg γc γm nodes.length fr nodes) ∗ ⌜alive.length = nodes.length⌝ }}

/-- `m.GetLeader(args, reply)`: some id (or `reply` unchanged), no error. -/
abbrev master.Master.GetLeader.spec : Prop :=
  ∀ (m : Loc) (γc γm : GName) (N : Nat) (args reply : Loc) (rv : replica.defs.GetLeaderReply),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.master ∗
      master.isMaster m γc γm N ∗ reply ↦ rv }}
    (App (App (Val (m @!! go.GoType.PointerType master.Master.ty @!! go!"GetLeader"))
      (Val #args)) (Val #reply))
  {{ RET #(interface.nil : GoInterface); ∃ id : w64, reply ↦ replica.defs.GetLeaderReply.mk id }}

end spec

section proof
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF]
variable [master.Assumptions] [dlog.Assumptions]

end proof

end Perennial.github_com.imdea_software.swiftpaxos

/-
Ported from dsverify-lab examples/swiftpaxos/proof/Spec/swiftnet/CodecFns.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
The specs of the kit's codec functions that the master's dispatch (`rpcCall_master_Master_*`,
`examples/swiftnet/rpc_gen.go`) calls: decoding the methods' arguments, encoding their replies
(change log C7, the master group's hub request 6). Owned by the codec group, which proves them
(with `kitCodecOk_holds`); the master's `rcvrOk` proof takes them as hypotheses.
-/
module

public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.swift.Wire
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Base

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section spec
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics]
variable [examples.swiftnet.Assumptions]

/-- `rpcDecodeAs_defs_RegisterArgs(data)` on a `RegisterArgs`' encoding. -/
abbrev examples.swiftnet.rpcDecodeAs_defs_RegisterArgs.spec : Prop :=
  ∀ (data : GoSlice) (dq : DFrac) (ip : GoString) (port : w64),
  {{ (data ↦*{dq} (sp.KitVal.registerArgs ip port).encode : IProp netDistGF) }}
    (App (Val (@! examples.swiftnet.rpcDecodeAs_defs_RegisterArgs)) (Val #data))
  {{ RET (PairV #(replica.defs.RegisterArgs.mk ip port) #(interface.nil : GoInterface));
      data ↦*{dq} (sp.KitVal.registerArgs ip port).encode }}

/-- `rpcDecodeAs_defs_GetReplicaListArgs(data)` on its encoding. -/
abbrev examples.swiftnet.rpcDecodeAs_defs_GetReplicaListArgs.spec : Prop :=
  ∀ (data : GoSlice) (dq : DFrac),
  {{ (data ↦*{dq} sp.KitVal.getReplicaListArgs.encode : IProp netDistGF) }}
    (App (Val (@! examples.swiftnet.rpcDecodeAs_defs_GetReplicaListArgs)) (Val #data))
  {{ RET (PairV #(replica.defs.GetReplicaListArgs.mk) #(interface.nil : GoInterface));
      data ↦*{dq} sp.KitVal.getReplicaListArgs.encode }}

/-- `rpcDecodeAs_defs_GetLeaderArgs(data)` on its encoding. -/
abbrev examples.swiftnet.rpcDecodeAs_defs_GetLeaderArgs.spec : Prop :=
  ∀ (data : GoSlice) (dq : DFrac),
  {{ (data ↦*{dq} sp.KitVal.getLeaderArgs.encode : IProp netDistGF) }}
    (App (Val (@! examples.swiftnet.rpcDecodeAs_defs_GetLeaderArgs)) (Val #data))
  {{ RET (PairV #(replica.defs.GetLeaderArgs.mk) #(interface.nil : GoInterface));
      data ↦*{dq} sp.KitVal.getLeaderArgs.encode }}

/-- `rpcPutU64(nil, x)`. -/
abbrev examples.swiftnet.rpcPutU64.specNil : Prop :=
  ∀ (x : w64),
  {{ (True : IProp netDistGF) }}
    (App (App (Val (@! examples.swiftnet.rpcPutU64)) (Val #slice.nil)) (Val #x))
  {{ (s : GoSlice), RET #s; s ↦* sp.cU64 x ∗ ownSliceCap w8 s (DFrac.own 1) }}

/-- `rpcEnc_defs_RegisterReply(b, v)`: appends `v`'s encoding. -/
abbrev examples.swiftnet.rpcEnc_defs_RegisterReply.spec : Prop :=
  ∀ (b : GoSlice) (bs : List w8) (v : replica.defs.RegisterReply) (ns : List GoString)
    (dq : DFrac),
  {{ (b ↦* bs ∗ ownSliceCap w8 b (DFrac.own 1) ∗ v.NodeList' ↦*{dq} ns : IProp netDistGF) }}
    (App (App (Val (@! examples.swiftnet.rpcEnc_defs_RegisterReply)) (Val #b)) (Val #v))
  {{ (b' : GoSlice), RET #b'; b' ↦* (bs ++ (sp.cU64 v.ReplicaId' ++ sp.cList sp.cBytes ns ++
        sp.cBool v.Ready' ++ sp.cBool v.IsLeader')) ∗ ownSliceCap w8 b' (DFrac.own 1) ∗
      v.NodeList' ↦*{dq} ns }}

/-- `rpcEnc_defs_GetReplicaListReply(b, v)`: appends `v`'s encoding. -/
abbrev examples.swiftnet.rpcEnc_defs_GetReplicaListReply.spec : Prop :=
  ∀ (b : GoSlice) (bs : List w8) (v : replica.defs.GetReplicaListReply) (rs : List GoString)
    (al : List Bool) (dq1 dq2 : DFrac),
  {{ (b ↦* bs ∗ ownSliceCap w8 b (DFrac.own 1) ∗ v.ReplicaList' ↦*{dq1} rs ∗
      v.AliveList' ↦*{dq2} al : IProp netDistGF) }}
    (App (App (Val (@! examples.swiftnet.rpcEnc_defs_GetReplicaListReply)) (Val #b)) (Val #v))
  {{ (b' : GoSlice), RET #b'; b' ↦* (bs ++ (sp.cList sp.cBytes rs ++ sp.cList sp.cBool al ++
        sp.cBool v.Ready')) ∗ ownSliceCap w8 b' (DFrac.own 1) ∗
      v.ReplicaList' ↦*{dq1} rs ∗ v.AliveList' ↦*{dq2} al }}

/-- `rpcEnc_defs_GetLeaderReply(b, v)`: appends `v`'s encoding. -/
abbrev examples.swiftnet.rpcEnc_defs_GetLeaderReply.spec : Prop :=
  ∀ (b : GoSlice) (bs : List w8) (v : replica.defs.GetLeaderReply),
  {{ (b ↦* bs ∗ ownSliceCap w8 b (DFrac.own 1) : IProp netDistGF) }}
    (App (App (Val (@! examples.swiftnet.rpcEnc_defs_GetLeaderReply)) (Val #b)) (Val #v))
  {{ (b' : GoSlice), RET #b'; b' ↦* (bs ++ sp.cU64 v.LeaderId') ∗
      ownSliceCap w8 b' (DFrac.own 1) }}

end spec

end Perennial.github_com.imdea_software.swiftpaxos

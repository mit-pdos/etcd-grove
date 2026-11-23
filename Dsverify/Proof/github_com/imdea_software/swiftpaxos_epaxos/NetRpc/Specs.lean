/-
The RPC layer's interfaces between its parts (statements only; tier "defs"):

* the clients' calls, as the kit's code makes them (`NetRpc/Calls.lean` proves them from Net's
  `Client.Call.spec` and `CodecLaws`): the master's `run` calls `Replica.BeTheLeader` and
  `Replica.Ping` (`btlCall.spec`, `pingCall.spec`), the kit's `register` calls
  `Master.Register` (`registerCall.spec`);
* the receivers' method bodies, over an abstract persistent handle (`isM m` the master's,
  `isR r` a replica's): `masterRegister.spec`, `masterGetLeader.spec`,
  `masterGetReplicaList.spec` (the master package's proofs, `master/`), `replicaBtl.spec`,
  `replicaPing.spec` (the epaxos package's);
* the receivers as `rpc.Register` takes them (`masterRcv.spec`, `replicaRcv.spec`: the codec's
  `rcv` gives `rcvrIs` with the service's spec; `NetRpc/Bindings.lean` proves them from the
  bodies, `SrvCodecLaws` and `ArgFacts`).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.NetRpc.CodecSrv
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.NetRpc.Methods
public import Dsverify.GeneratedProof.github_com.imdea_software.swiftpaxos_epaxos.master
public import Dsverify.GeneratedProof.github_com.imdea_software.swiftpaxos_epaxos.epaxos
public import Net.Proof.net.rpc.ClientDefs

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net
open github_com.imdea_software.swiftpaxos_epaxos.netrpcw

namespace github_com.imdea_software.swiftpaxos_epaxos

section specs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [net.rpc.Assumptions] [net.FieldAssumptions] [π : NetProtoGS]
variable [examples.epaxosnet.Assumptions] [master.Assumptions] [epaxos.Assumptions]

attribute [local instance] GooseGlobalGS.gooseInvGS

/-! ## The clients' calls -/

/-- `cl.Call("Replica.BeTheLeader", &defs.BeTheLeaderArgs{}, btlReply)` (the master's `run`):
a reply decodes into `btlReply`'s fields as they were (the method sends the zero reply); on an
error too, `btlReply` is as it was: Go's `Call` decodes into it only the server's reply, which is
the zero reply's bytes, whose decoding succeeds (a failed decoding could leave a partial value;
the master's `run` reads `btlReply.Leader` after a failed call and indexes `leader` with it, so a
spec allowing any value there would let it panic). -/
abbrev btlCall.spec : Prop :=
  ∀ (W : net.rpc.RpcWorld GF) (k : Nat) (cl la bl : Loc) (l0 nl0 : w32),
    k ∈ replicaNodes → W.SS (rpcAddrOf k) go!"Replica" = some replicaSvc →
  {{ rpcReady ∗ net.rpc.isClient cl W (rpcAddrOf k) ∗ la ↦ replica.defs.BeTheLeaderArgs.mk ∗
      bl ↦ replica.defs.BeTheLeaderReply.mk l0 nl0 }}
    (App (App (App (Val (cl @!! go.GoType.PointerType net.rpc.Client.ty @!! go!"Call"))
      (Val #(go!"Replica.BeTheLeader")))
      (Val #(ptrIface replica.defs.BeTheLeaderArgs.ty la)))
      (Val #(ptrIface replica.defs.BeTheLeaderReply.ty bl)))
  {{ (err : GoInterface), RET #err;
      (⌜err = interface.nil⌝ ∗ bl ↦ replica.defs.BeTheLeaderReply.mk l0 nl0) ∨
      (⌜err ≠ interface.nil⌝ ∗ bl ↦ replica.defs.BeTheLeaderReply.mk l0 nl0) }}

/-- `cl.Call("Replica.Ping", &defs.PingArgs{}, &defs.PingReply{})` (the master's `run`). -/
abbrev pingCall.spec : Prop :=
  ∀ (W : net.rpc.RpcWorld GF) (k : Nat) (cl la lr : Loc),
    k ∈ replicaNodes → W.SS (rpcAddrOf k) go!"Replica" = some replicaSvc →
  {{ rpcReady ∗ net.rpc.isClient cl W (rpcAddrOf k) ∗ la ↦ replica.defs.PingArgs.mk (W8 0) ∗
      lr ↦ replica.defs.PingReply.mk }}
    (App (App (App (Val (cl @!! go.GoType.PointerType net.rpc.Client.ty @!! go!"Call"))
      (Val #(go!"Replica.Ping")))
      (Val #(ptrIface replica.defs.PingArgs.ty la)))
      (Val #(ptrIface replica.defs.PingReply.ty lr)))
  {{ (err : GoInterface), RET #err; True }}

/-- `mcli.Call("Master.Register", args, &reply)` (the kit's `register`, replica node `k`; the
arguments are read-only, reused across calls). -/
abbrev registerCall.spec : Prop :=
  ∀ (γ : EpNames) (W : net.rpc.RpcWorld GF) (k : Nat) (cl pa pr : Loc),
    k ∈ replicaNodes → W.SS masterAddr go!"Master" = some (masterSvc γ) →
  {{ rpcReady ∗ net.rpc.isClient cl W masterAddr ∗
      pa ↦□ replica.defs.RegisterArgs.mk (replicaIp k) (portOf k) ∗
      pr ↦ replica.defs.RegisterReply.mk (W64 0) slice.nil false false }}
    (App (App (App (Val (cl @!! go.GoType.PointerType net.rpc.Client.ty @!! go!"Call"))
      (Val #(go!"Master.Register")))
      (Val #(ptrIface replica.defs.RegisterArgs.ty pa)))
      (Val #(ptrIface replica.defs.RegisterReply.ty pr)))
  {{ (err : GoInterface), RET #err;
      (⌜err = interface.nil⌝ ∗ ∃ (id : w64) (sl : GoSlice) (nl : List GoString) (r il : Bool),
        pr ↦ replica.defs.RegisterReply.mk id sl r il ∗ sl ↦* nl ∗ regReplyOk γ k id nl r) ∨
      (⌜err ≠ interface.nil⌝ ∗ ∃ v : replica.defs.RegisterReply, pr ↦ v) }}

/-! ## The receivers' method bodies -/

/-- `m.Register(args, reply)` on the master `isM m`, called by replica node `k`. -/
abbrev masterRegister.spec (γ : EpNames) (isM : Loc → IProp GF) : Prop :=
  ∀ (m : Loc) (k : Nat) (pa pr : Loc), k ∈ replicaNodes →
  {{ isM m ∗ pa ↦ replica.defs.RegisterArgs.mk (replicaIp k) (portOf k) ∗
      pr ↦ replica.defs.RegisterReply.mk (W64 0) slice.nil false false }}
    (App (App (Val (m @!! go.GoType.PointerType master.Master.ty @!! go!"Register")) (Val #pa))
      (Val #pr))
  {{ RET #(interface.nil : GoInterface);
      ∃ (id : w64) (sl : GoSlice) (dq : DFrac) (nl : List GoString) (r il : Bool),
        pr ↦ replica.defs.RegisterReply.mk id sl r il ∗ sl ↦*{dq} nl ∗ regReplyOk γ k id nl r }}

/-- `m.GetLeader(args, reply)`. -/
abbrev masterGetLeader.spec (isM : Loc → IProp GF) : Prop :=
  ∀ (m pa pr : Loc),
  {{ isM m ∗ pa ↦ replica.defs.GetLeaderArgs.mk ∗ pr ↦ replica.defs.GetLeaderReply.mk (W64 0) }}
    (App (App (Val (m @!! go.GoType.PointerType master.Master.ty @!! go!"GetLeader")) (Val #pa))
      (Val #pr))
  {{ RET #(interface.nil : GoInterface); ∃ id : w64, pr ↦ replica.defs.GetLeaderReply.mk id }}

/-- `m.GetReplicaList(args, reply)`. -/
abbrev masterGetReplicaList.spec (isM : Loc → IProp GF) : Prop :=
  ∀ (m pa pr : Loc),
  {{ isM m ∗ pa ↦ replica.defs.GetReplicaListArgs.mk ∗
      pr ↦ replica.defs.GetReplicaListReply.mk slice.nil slice.nil false }}
    (App (App (Val (m @!! go.GoType.PointerType master.Master.ty @!! go!"GetReplicaList"))
      (Val #pa)) (Val #pr))
  {{ RET #(interface.nil : GoInterface);
      ∃ (sr sa : GoSlice) (rl : List GoString) (al : List Bool) (r : Bool),
        pr ↦ replica.defs.GetReplicaListReply.mk sr sa r ∗ sr ↦* rl ∗ sa ↦* al }}

/-- `r.BeTheLeader(args, reply)` on the replica `isR r`: the reply untouched. -/
abbrev replicaBtl.spec (isR : Loc → IProp GF) : Prop :=
  ∀ (r pa pr : Loc),
  {{ isR r ∗ pa ↦ replica.defs.BeTheLeaderArgs.mk ∗
      pr ↦ replica.defs.BeTheLeaderReply.mk (W32 0) (W32 0) }}
    (App (App (Val (r @!! go.GoType.PointerType epaxos.Replica.ty @!! go!"BeTheLeader"))
      (Val #pa)) (Val #pr))
  {{ RET #(interface.nil : GoInterface); pr ↦ replica.defs.BeTheLeaderReply.mk (W32 0) (W32 0) }}

/-- `r.Ping(args, reply)` (the framework's, promoted): nothing touched. -/
abbrev replicaPing.spec (isR : Loc → IProp GF) : Prop :=
  ∀ (r pa pr : Loc) (a : w8),
  {{ isR r ∗ pa ↦ replica.defs.PingArgs.mk a ∗ pr ↦ replica.defs.PingReply.mk }}
    (App (App (Val (r @!! go.GoType.PointerType epaxos.Replica.ty @!! go!"Ping"))
      (Val #pa)) (Val #pr))
  {{ RET #(interface.nil : GoInterface); pr ↦ replica.defs.PingReply.mk }}

/-! ## The receivers -/

/-- The master `m` as `rpc.Register(m)` takes it: the codec's `rcv` gives the receiver with the
`Master` service's spec (the registered codec, which `Server.Register` also asks for, is what
the methods' argument decoding, Net's `argDec`, offers). -/
abbrev masterRcv.spec (γ : EpNames) (isM : Loc → IProp GF) : Prop :=
  ∀ (m : Loc), ⌜m ≠ null⌝ ∗ net.rpc.codecSet epCodec ∗ isM m ⊢
    epCodec.rcv (ptrIface master.Master.ty m)
      (net.rpc.rcvrIs epCodec (ptrIface master.Master.ty m) (masterSvc γ) go!"Master" false)

/-- A replica `r` as `rpc.Register(rep)` takes it. -/
abbrev replicaRcv.spec (isR : Loc → IProp GF) : Prop :=
  ∀ (r : Loc), ⌜r ≠ null⌝ ∗ net.rpc.codecSet epCodec ∗ isR r ⊢
    epCodec.rcv (ptrIface epaxos.Replica.ty r)
      (net.rpc.rcvrIs epCodec (ptrIface epaxos.Replica.ty r) replicaSvc go!"Replica" false)

end specs

end github_com.imdea_software.swiftpaxos_epaxos

end Perennial

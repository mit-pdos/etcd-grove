/-
# Raft's API module (2026-10-26, stage 1: the node API)


What a proof outside raft may use of raft's proof: import this module, and nothing of raft's
`Proof/` tree but what it lists (`etc/api-check.py etc/api/raft.txt --check`;
`notes/decisions.md`, "Package signatures").

**The specs** (`Spec/go_etcd_io/raft/v3/`): `StartNode`, `RestartNode` and the `Node` interface's
methods (`node.Propose`, `ProposeConfChange`, `Step`, `Ready`, `Advance`, `ApplyConfChange`,
`Tick`, `ReadIndex`, `TransferLeadership`, `ForgetLeader`, `ReportSnapshot`, `ReportUnreachable`),
`MemoryStorage`'s, and the helpers `IsEmptyHardState`, `IsEmptySnap`. Their linked results, for a
proof that uses one as a lemma rather than taking it as a callee's spec, are
`Proof/go_etcd_io/raft/v3/Linked.lean`'s (`RaftLink`).

**The vocabulary** the specs and the laws are stated in:
- `Proof/go_etcd_io/raft/v3/InvNode.lean` and `InvNodeCtx.lean`, the node API: the node and its
  driver's tokens (`isNodeChan`, `nodeDriverChan`, `nodeDriverBusy`, `nodeCfg`, `dlvLb`) and the `Ready`
  channel's payload (`readyP`, `isReadyChanRaw`) are **sealed** (`@[no_expose]`): a client sees their
  names, never their bodies -- the node struct's channels, their protocols and the ghost state
  between `run` and the driver. What the client receives or must build is transparent: a
  `Ready`'s data (`readyData`, `readySnapData`, `readyDataL`), a message to step (`stepP`, `netP`,
  `fwdP`), a proposal (`propArg`, `ccPropArg`, keyed by `entKey`), the term budget (`budgetInv`,
  `termLB`, `tickCred`), the errors (`InvNodeCtx`);
- `Proof/go_etcd_io/raft/v3/ApiVocab.lean`: the records and predicates of those statements that
  raft's internals also use (`QMsg`, `SnapLoan`, `RNMode`, `RNState`, `NetMsgOk`, `SentMsgOk`,
  `isRaftMsg`, `readyIdx`, `bootInit`, `ConfigValid`, ...);
- the modules of raft's tree these import publicly, which a later stage brings under the
  signature: the protocol's ghost vocabulary (`Protocol/*`: `RaftNames`, `isCommitted`, the
  proposal deposits, the read index), the protobuf model (`InvPb*`), the `Storage` contract
  (`InvStorage`) and `MemoryStorage`'s predicates (`InvMemstorage`).

**The laws** of the sealed predicates are theorems of `InvNode.lean` (e.g. `isNode_id`,
`isNode_commitInv`, `nodeDriver_isNode`, `readyP_take`, `readyP_take_ns`, `node_ready_receive`,
`node_prop_register`, `node_committed_data`, `node_read_deposit`, `budget_alloc`); a client can
prove nothing else of a sealed predicate. Raft's own proofs see the bodies (`import all
Proof.go_etcd_io.raft.v3.InvNodeChan`).

**Sealed below the API** (internal: no client module may import them, even transitively):
`InvRawnode`, `InvRawnodeReady`, `InvRawnodeC`, `InvNodeRun`, `InvBoot`, `InvRaftPhys` and
everything importing them -- the `RawNode`'s invariant (`ownRawNode`), the raft struct's
(`ownRaftPhys`), `node.go`'s run loop. The `RawNode` API's specs are stated over them and are not
part of the signature yet.
-/
module

public import Spec.go_etcd_io.raft.v3.StartNode
public import Spec.go_etcd_io.raft.v3.RestartNode
public import Spec.go_etcd_io.raft.v3.node__Propose
public import Spec.go_etcd_io.raft.v3.node__ProposeConfChange
public import Spec.go_etcd_io.raft.v3.node__Step
public import Spec.go_etcd_io.raft.v3.node__Ready
public import Spec.go_etcd_io.raft.v3.node__Advance
public import Spec.go_etcd_io.raft.v3.node__ApplyConfChange
public import Spec.go_etcd_io.raft.v3.node__Tick
public import Spec.go_etcd_io.raft.v3.node__ReadIndex
public import Spec.go_etcd_io.raft.v3.node__TransferLeadership
public import Spec.go_etcd_io.raft.v3.node__ForgetLeader
public import Spec.go_etcd_io.raft.v3.node__ReportSnapshot
public import Spec.go_etcd_io.raft.v3.node__ReportUnreachable
public import Spec.go_etcd_io.raft.v3.IsEmptyHardState
public import Spec.go_etcd_io.raft.v3.IsEmptySnap
public import Spec.go_etcd_io.raft.v3.NewMemoryStorage
public import Proof.go_etcd_io.raft.v3.InvNodeChan
public import Proof.go_etcd_io.raft.v3.InvNodeCtx
public import Proof.go_etcd_io.raft.v3.ApiVocab

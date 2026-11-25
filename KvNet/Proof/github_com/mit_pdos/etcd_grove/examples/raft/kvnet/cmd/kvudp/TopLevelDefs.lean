/-
# `raft/kvnet/cmd/kvudp`: the definitions its top-level statement is written in (2026-11-24)

kvudp is kvnet with the replicas' raft messages over UDP (`kvnet.RunNodeUDP`; the clients' requests
still over TCP): the programs its top-level theorem is about, here so that the statement
(`KvNet/Spec/.../kvnet/cmd/kvudp/TopLevelRobustness.lean`) imports no proof. Everything else it names is
kvnet's audited vocabulary (`raft_kvnet.ClusterConfig`, `ClusterConfig.Ok`, kvnet's `TopLevelDefs.lean`),
reused unchanged; the programs and `fsOf` are restated only because their extensions differ
(`[netExt, fsExt, udpExt]`, `NetFsUdp.kvudpExts`).

* `kvudpReplicaProgram cl addrs dir id`: replica `id`'s process, kvnet's package initialization, then
  `RunNodeUDP` (as `kvnetReplicaProgram`, with `RunNodeUDP` for `RunNode`).
* `kvudpCheckProgram cl addrs`: the checking client's process, as `kvcheckProgram` (the same body).
* `fsOf σ`: a machine's Linux file system (the file extension's local state).
* `kvudpThreads`: the statement's thread bound (`Robust`'s `threads`).
-/
module

public import GooseLang.Ext.NetFsUdp.Adequacy
public import KvNet.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.TopLevelDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace raft_kvudp

open NetFsUdp raft_kvnet

section programs
attribute [local instance] kvudpExts
variable [go_gctx : GoGlobalContext]

/-- Replica `id`'s process: kvnet's package initialization, then `RunNodeUDP`; `addrs` the replicas'
addresses joined by commas (replica `i` at the `i`-th: its TCP listener's and its UDP socket's), `dir`
the directory of its durable state (the storage file and the boot counter's). -/
def kvudpReplicaProgram [GoSemanticsFunctions] (cl : ClusterConfig) (addrs dir : GoString)
    (id : w64) : Expr :=
  github_com.mit_pdos.etcd_grove.examples.raft.kvnet.initialize' #() ;;
  (@! github_com.mit_pdos.etcd_grove.examples.raft.kvnet.RunNodeUDP) #id #addrs #dir #cl.voters
    #cl.preVote #cl.checkQuorum #cl.stepDownOnRemoval #cl.maxSizePerMsg
    #cl.maxCommittedSizePerReady #cl.maxInflightMsgs

/-- The checking client's process: its package initialization, then `Check` (kvnet's
`kvcheckProgram`, over kvudp's extensions). -/
def kvudpCheckProgram [GoSemanticsFunctions] (cl : ClusterConfig) (addrs : GoString) : Expr :=
  github_com.mit_pdos.etcd_grove.examples.raft.kvnet.kvcheck.initialize' #() ;;
  (@! github_com.mit_pdos.etcd_grove.examples.raft.kvnet.kvcheck.Check) #addrs #cl.voters

end programs

section fs
attribute [local instance] kvudpExts kvudpExtsSemantics kvudpExts_hasFs

/-- A machine's Linux file system: the file extension's local state. -/
abbrev fsOf (σ : state) : Fs.OsState := extLocal Fs.fsExt σ.world

end fs

/-- **The statement's thread bound** (`Robust`'s `threads`): the live threads (`state.threads`) a
machine keeps fewer of, along the executions the theorem covers. kvudp's proof needs no thread
bound: no spec it rests on takes the machine's `threadBound` (no counter backed by thread tokens,
such as a `sync.WaitGroup`'s or an `RWMutex`'s readers'), and the program's goroutines are not
bounded by a constant anyway (a replica forks one per accepted TCP connection, `Node.accept`, and
one per snapshot it sends over UDP, `udpTransport`'s `sendSnapshot`). So the bound is set to exclude
nothing: a machine starts with one thread and a step forks at most one, so in fewer than `2 ^ 61`
steps (the statement's step bound) it never reaches `2 ^ 61 + 1` threads. -/
def kvudpThreads : Nat := 2 ^ 61 + 1

end raft_kvudp
end EtcdGrove
end Perennial

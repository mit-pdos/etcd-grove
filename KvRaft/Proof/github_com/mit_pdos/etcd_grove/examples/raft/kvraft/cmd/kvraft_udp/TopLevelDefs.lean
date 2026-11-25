/-
# `raft/kvraft/cmd/kvraft-udp`: the definitions its top-level statement is written in (2026-11-24)

kvraft-udp is kvraft with the replicas' raft messages over UDP (`kvraft.RunNodeUDP`; the clients' requests
still over TCP): the programs its top-level theorem is about, here so that the statement
(`KvRaft/Spec/.../kvraft/cmd/kvraft_udp/TopLevelRobustness.lean`) imports no proof. Everything else it names is
kvraft's audited vocabulary (`kvraft.ClusterConfig`, `ClusterConfig.Ok`, kvraft's `TopLevelDefs.lean`),
reused unchanged; the programs and `fsOf` are restated only because their extensions differ
(`[netExt, fsExt, udpExt]`, `NetFsUdp.kvraftUdpExts`).

* `kvraftUdpReplicaProgram cl addrs dir id`: replica `id`'s process, kvraft's package initialization, then
  `RunNodeUDP` (as `kvraftReplicaProgram`, with `RunNodeUDP` for `RunNode`).
* `kvraftUdpCheckProgram cl addrs`: the checking client's process, as `kvcheckProgram` (the same body).
* `fsOf σ`: a machine's Linux file system (the file extension's local state).
* `kvraftUdpThreads`: the statement's thread bound (`Robust`'s `threads`).
-/
module

public import GooseLang.Ext.NetFsUdp.Adequacy
public import KvRaft.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.TopLevelDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvraft_udp

open NetFsUdp kvraft

section programs
attribute [local instance] kvraftUdpExts
variable [go_gctx : GoGlobalContext]

/-- Replica `id`'s process: kvraft's package initialization, then `RunNodeUDP`; `addrs` the replicas'
addresses joined by commas (replica `i` at the `i`-th: its TCP listener's and its UDP socket's), `dir`
the directory of its durable state (the storage file and the boot counter's). -/
def kvraftUdpReplicaProgram [GoSemanticsFunctions] (cl : ClusterConfig) (addrs dir : GoString)
    (id : w64) : Expr :=
  github_com.mit_pdos.etcd_grove.examples.raft.kvraft.initialize' #() ;;
  (@! github_com.mit_pdos.etcd_grove.examples.raft.kvraft.RunNodeUDP) #id #addrs #dir #cl.voters
    #cl.preVote #cl.checkQuorum #cl.stepDownOnRemoval #cl.maxSizePerMsg
    #cl.maxCommittedSizePerReady #cl.maxInflightMsgs

/-- The checking client's process: its package initialization, then `Check` (kvraft's
`kvcheckProgram`, over kvraft-udp's extensions). -/
def kvraftUdpCheckProgram [GoSemanticsFunctions] (cl : ClusterConfig) (addrs : GoString) : Expr :=
  github_com.mit_pdos.etcd_grove.examples.raft.kvraft.kvcheck.initialize' #() ;;
  (@! github_com.mit_pdos.etcd_grove.examples.raft.kvraft.kvcheck.Check) #addrs #cl.voters

end programs

section fs
attribute [local instance] kvraftUdpExts kvraftUdpExtsSemantics kvraftUdpExts_hasFs

/-- A machine's Linux file system: the file extension's local state. -/
abbrev fsOf (σ : state) : Fs.OsState := extLocal Fs.fsExt σ.world

end fs

/-- **The statement's thread bound** (`Robust`'s `threads`): the live threads (`state.threads`) a
machine keeps fewer of, along the executions the theorem covers. kvraft-udp's proof needs no thread
bound: no spec it rests on takes the machine's `threadBound` (no counter backed by thread tokens,
such as a `sync.WaitGroup`'s or an `RWMutex`'s readers'), and the program's goroutines are not
bounded by a constant anyway (a replica forks one per accepted TCP connection, `Node.accept`, and
one per snapshot it sends over UDP, `udpTransport`'s `sendSnapshot`). So the bound is set to exclude
nothing: a machine starts with one thread and a step forks at most one, so in fewer than `2 ^ 61`
steps (the statement's step bound) it never reaches `2 ^ 61 + 1` threads. -/
def kvraftUdpThreads : Nat := 2 ^ 61 + 1

end kvraft_udp
end EtcdGrove
end Perennial

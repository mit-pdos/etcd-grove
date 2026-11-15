/-
Lean-first (no Rocq counterpart).

# kvnet's robustness statement (2026-11-15; no proof yet)

`examples/raft/kvnet` (`notes/kvnet.md`): kvdurable's replicated key-value store on raft, every
replica a process of its own, talking to its peers and its clients over TCP, its durable state one
file. Its test (`examples/raft/kvnet/driver`, over the harness `examples/lib/robust`) runs the
replicas' unchanged binary on machines of their own while the environment kills them, cuts their
disks' power, partitions and degrades the network, and clients on other machines call `Put`, `Get`
and `Read`; it checks the clients' history with porcupine. `kvnetRobust` is what a proof of the
replica program would establish of every such run, over the generic statement of
`Robustness/Statement.lean`:

**For every deployment** of replica processes, each running `prog cfg` (its node configuration
`cfg`: id, directory, every replica's address, the cluster's options) on a machine of its own, at
the start and after every crash, with an empty directory of its own and no package initialized;
with any number of environment nodes running **any programs** on other hosts, with no listener at
the start; on a fresh network (no connection) with a well-formed plan of addresses that puts each
replica's address on its machine; **in every run** (`IsRun`, the executions of Perennial's
`DistCrashStep`: any interleaving, any crash of any node at any step -- a power loss, or a kill
followed by a sync, the file extension's "Restarts" -- and every network fault the TCP semantics
allows: bytes delayed, directions cut, dials failing, which is what partitions and resets are) of
fewer than `2^61` steps,
**if the environment's events** (`ClientsOk`) never speak the peer protocol to a replica (a
connection a client opens to a replica starts with `'C'`) and never send two read requests with
one sequence number, **then** no replica is stuck or has an unrecovered panic, and the clients'
operations as the network shows them (`kvProto`: a request frame on a connection to a replica, its
answer frame) are linearizable for the store's model (`kvModel`), operations that never got an
answer taking effect or not.

What the statement does **not** assume of clients: well-formed requests (garbage gets no answer),
fresh proposal ids (a proposal is identified by its whole payload, which the replicas
deduplicate: a client that sends one payload twice gets one operation, answered alike), anything
about configuration changes, disruptions or status requests (any of them, at any time, to any
replica). Peers' messages are not checked by the replicas, so a client speaking the peer protocol
could forge raft messages: that is the closed-world assumption `NoPeerClaim`.

**The parameters a proof will fix.**
* `prog`: the Goose translation of a replica's process, kvnet's package initialization then
  `RunNode(cfg)` with `cfg`'s Go value. kvnet is not translated yet, so the statement takes it as
  a parameter: `kvnetRobust (fun cfg => <translated program>)` is the theorem to prove.
* The extensions: any list of them with the TCP extension (`[HasExt Tcp.tcpExt]`,
  `GooseLang/Ext/Tcp/Impl.lean`: the network, whose events `Robustness/Stream.lean` reads off its
  state) and the Linux file extension (`[HasExt Fs.fsExt]`: the replicas' file, written through
  `durable.Write`, reimplemented over `os` per `notes/decisions.md`, "One file semantics, fsExt;
  power loss only"), each with its own semantics (`HasExt.sem_eq`).

The wire format below is kvnet's (`wire.go`, `client.go`, `codec.go`): a frame is an 8-byte
little-endian length and the body (a reader drops a length above `2^26`); a client connection
starts with `'C'`, then one request frame (kind, an 8-byte timeout, the payload), answered by one
frame (`1` and the answer, or `0`: no answer).
-/
module

public import Robustness.Stream
public import GooseLang.Ext.Fs.Ghost
public import GooseLang.Ext.Tcp.Ghost
public import GooseLang.Ext.Tcp.Deploy
public import Perennial.Golang.Defn

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace raft_kvnet

open Robustness github_com.anishathalye.porcupine

/-! ## The wire -/

/-- An 8-byte little-endian number at the start of `b`, and the rest. -/
def u64le (b : List w8) : Option (Nat × List w8) :=
  if b.length < 8 then none
  else some ((b.take 8).foldr (fun x acc => x.toNat + 256 * acc) 0, b.drop 8)

/-- `maxFrame`: a reader drops a connection that announces a longer frame. -/
def maxFrame : Nat := 2 ^ 26

/-- The body of the frame at the start of `b` (`readFrame`), once all of it is there. -/
def frame (b : List w8) : Option (List w8) := do
  let (n, rest) ← u64le b
  if n ≤ maxFrame ∧ n ≤ rest.length then some (rest.take n) else none

/-- What a client connection starts with (`helloClient`, `'C'`). -/
def helloClient : w8 := 67

/-- The request kinds (`ReqPropose`, `ReqRead`). -/
def reqPropose : w8 := 1
def reqRead : w8 := 2

/-- The store's operation kind `opPut`. -/
def opPut : w8 := 1

/-! ## Operations and the store's model -/

/-- An operation's identity: a proposal by its whole payload (the replicas deduplicate a proposal
by it: `Replica.applyOp`, `Replica.propose`), a read by its sequence number. -/
inductive OpKey where
  | prop (payload : List w8)
  | read (seq : Nat)
deriving DecidableEq

/-- An operation's input: a `Put` of a key's value, or a read of a key (a `Get` through the log,
a proposal of any other kind, or a `Read` by a read index). -/
inductive KVIn where
  | put (key val : List w8)
  | get (key : List w8)

/-- The store's sequential model (kvnet's `Model()`): a map from keys to values, a key it lacks
having the value `[]`; a `Put` sets its key's value and answers it (the replica answers a proposal
with its key's value once applied: the value it put); a read answers its key's value. -/
def kvModel : Theory.SeqModel (List w8 → List w8) (KVIn × List w8) where
  init := fun _ => []
  step s
    | (.put k v, out) => if out = v then some (fun k' => if k' = k then v else s k') else none
    | (.get k, out) => if out = s k then some s else none

/-- A proposal's operation, from its payload (`decode`: an 8-byte id, the kind, the key's 8-byte
length, the key, then the value, the rest). -/
def proposal (p : List w8) : Option KVIn := do
  let (_, r1) ← u64le p
  match r1 with
  | [] => none
  | k :: r2 =>
    let (n, r3) ← u64le r2
    if n ≤ r3.length then
      some (if k = opPut then .put (r3.take n) (r3.drop n) else .get (r3.take n))
    else none

/-- A read's sequence number and key, from its payload (an 8-byte sequence number, then the key
as `putBytes` writes it; the rest ignored). -/
def readReq (p : List w8) : Option (Nat × List w8) := do
  let (seq, r1) ← u64le p
  let (n, r2) ← u64le r1
  if n ≤ r2.length then some (seq, r2.take n) else none

/-- kvnet's client protocol, at the replicas' addresses `addrs`: a connection to one of them whose
dialer wrote `'C'` and a complete request frame of a proposal or a read is that operation; an
answer frame `1 :: ans` answers it with `ans`. -/
def kvProto (addrs : List GoString) : ReqResp OpKey KVIn (List w8) where
  req a bs := do
    if a ∉ addrs then none else
    match bs with
    | c :: rest =>
      if c ≠ helloClient then none else
      let body ← frame rest
      match body with
      | kind :: r1 =>
        let (_, payload) ← u64le r1
        if kind = reqPropose then (proposal payload).map fun i => (.prop payload, i)
        else if kind = reqRead then (readReq payload).map fun (seq, k) => (.read seq, .get k)
        else none
      | [] => none
    | [] => none
  resp bs := match frame bs with
    | some (1 :: ans) => some ans
    | _ => none

/-! ## The environment's discipline -/

/-- No client speaks the peer protocol to a replica: every connection to a replica's address into
which the environment writes as the dialer starts with `'C'` (the closed world: the replicas do
not check who sends raft messages). -/
def NoPeerClaim (addrs : List GoString) (evs : List StreamEv) : Prop :=
  ∀ e ∈ evs, e.addr ∈ addrs → e.fromAcceptor = false →
    (streamBytes evs e.conn false).head? = some helloClient

/-- No two read requests carry one sequence number (a replica matches a read's answer to its
waiter by it: `Replica.read`). -/
def ReadSeqsFresh (addrs : List GoString) (evs : List StreamEv) : Prop :=
  ∀ e ∈ evs, ∀ e' ∈ evs, ∀ seq i i',
    (kvProto addrs).req e.addr (streamBytes evs e.conn false) = some (.read seq, i) →
    (kvProto addrs).req e'.addr (streamBytes evs e'.conn false) = some (.read seq, i') →
    e.conn = e'.conn

/-- What the statement assumes of the environment's events. -/
def ClientsOk (addrs : List GoString) (evs : List StreamEv) : Prop :=
  NoPeerClaim addrs evs ∧ ReadSeqsFresh addrs evs

/-! ## The deployment -/

/-- The cluster's options (kvnet's `Options`). -/
structure Options where
  voters : Nat
  preVote : Bool
  checkQuorum : Bool
  stepDownOnRemoval : Bool
  maxSizePerMsg : Nat
  maxCommittedSizePerReady : Nat
  maxInflightMsgs : Nat

/-- A replica's configuration (kvnet's `NodeConfig`): its id, the directory of its file, every
replica's address by id (its own included), the options. -/
structure NodeConfig where
  id : Nat
  dir : GoString
  addrs : List (Nat × GoString)
  opts : Options

/-- The options raft accepts (`raft.Config.validate`: a positive `MaxInflightMsgs`; not both size
limits `0`, which `newRaft` refuses) and kvnet's (`1 ≤ voters`), within Go's integers. -/
def OptionsOk (o : Options) : Prop :=
  1 ≤ o.voters ∧ o.voters < 2 ^ 64 ∧ ¬ (o.maxSizePerMsg = 0 ∧ o.maxCommittedSizePerReady = 0) ∧
  o.maxSizePerMsg < 2 ^ 64 ∧ o.maxCommittedSizePerReady < 2 ^ 64 ∧
  0 < o.maxInflightMsgs ∧ o.maxInflightMsgs < 2 ^ 63

/-- The replicas' configurations agree on the addresses and options; their ids are distinct, each
nonzero, below `2^64`, with an address; no id or address is listed twice. -/
def ClusterOk (cfgs : List NodeConfig) : Prop :=
  (∀ c ∈ cfgs, ∀ c' ∈ cfgs, c.addrs = c'.addrs ∧ c.opts = c'.opts) ∧
  (cfgs.map NodeConfig.id).Nodup ∧
  (∀ c ∈ cfgs, 1 ≤ c.id ∧ c.id < 2 ^ 64 ∧ ∃ a, (c.id, a) ∈ c.addrs) ∧
  (∀ c ∈ cfgs, (c.addrs.map Prod.fst).Nodup ∧ (c.addrs.map Prod.snd).Nodup ∧
    (∀ p ∈ c.addrs, 1 ≤ p.1 ∧ p.1 < 2 ^ 64) ∧ OptionsOk c.opts)

/-- Every replica's address (from any configuration: they agree). -/
def replicaAddrs (cfgs : List NodeConfig) : List GoString :=
  cfgs.flatMap fun c => c.addrs.map Prod.snd

section deployment
variable [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext] [HasExt Fs.fsExt]
  [HasExt Tcp.tcpExt]

/-- The host of the machine with the local state `σ`. -/
abbrev hostOf (σ : state) : GoString := (extLocal Tcp.tcpExt σ.world).host

/-- The machine with the local state `σ` has no listener. -/
abbrev NoListener (σ : state) : Prop := (extLocal Tcp.tcpExt σ.world).lis = ∅

/-- The network at the start: the plan `plan` (each address and the host that may listen at it),
well formed (`Tcp.PlanWellFormed`, the TCP extension's deployment, D13 and D20), and no
connection. -/
def FreshNet (plan : List (GoString × GoString)) (g : GlobalState) : Prop :=
  Tcp.PlanWellFormed plan ∧ (netOf g).plan = GMap.ofList plan ∧ (netOf g).conns = ∅

/-- A replica's machine at the deployment's start: the Go context `lctx`, no package initialized,
the main thread only; its files as on disk, its directory one of the file system's roots and
empty; no listener; and every replica address in the plan, its own at its host. -/
def ReplicaStart (lctx : GoLocalContext) (plan : List (GoString × GoString)) (cfg : NodeConfig)
    (σ : state) : Prop :=
  σ.goState.goLctx = lctx ∧ σ.goState.packageState = ∅ ∧ σ.threads = 1 ∧
  Fs.FsInit (extLocal Fs.fsExt σ.world) ∧
  (∃ j, (cfg.dir, j) ∈ (extLocal Fs.fsExt σ.world).fs.roots) ∧
  (∀ c, (extLocal Fs.fsExt σ.world).lookup (joinPath cfg.dir [c]) = none) ∧
  NoListener σ ∧
  (∀ p ∈ cfg.addrs, ∃ h, (p.2, h) ∈ plan) ∧
  (∀ a, (cfg.id, a) ∈ cfg.addrs → (a, hostOf σ) ∈ plan)

/-- An environment node's machine: on a host where the plan puts no replica's address, with no
listener (so it can listen at no replica's address, now or later: `Tcp.ListenStep` listens only
at a plan address of the node's host, and a crash keeps the host). Nothing else is assumed of it:
any program, any other state. -/
def EnvStart (cfgs : List NodeConfig) (plan : List (GoString × GoString)) (σ : state) : Prop :=
  NoListener σ ∧ ∀ a h, (a, h) ∈ plan → a ∈ replicaAddrs cfgs → h ≠ hostOf σ

/-- **kvnet's robustness statement** (see the file header), for the replica program `prog`: every
deployment of replicas configured by `cfgs`, on machines `sys`, with any environment nodes `env`,
on a fresh network with the plan `plan`, is `Robust`: in every run of fewer than `2^61` steps in
which the events of the environment's steps satisfy `ClientsOk`, no replica is stuck or has an
unrecovered panic, and the clients' operations, as the network's events show them, are
linearizable for `kvModel`. -/
def kvnetRobust [lctx : GoLocalContext] [go.Semantics] (prog : NodeConfig → Expr) : Prop :=
  ∀ (cfgs : List NodeConfig) (sys : List state) (env : List (Expr × state))
    (plan : List (GoString × GoString)) (g : GlobalState),
    ClusterOk cfgs → cfgs.length = sys.length →
    (∀ p ∈ cfgs.zip sys, ReplicaStart lctx plan p.1 p.2) →
    (∀ x ∈ env, EnvStart cfgs plan x.2) →
    FreshNet plan g →
    Robust ((cfgs.zip sys).map (fun p => (prog p.1, p.2))) env g (2 ^ 61)
      (fun steps => ClientsOk (replicaAddrs cfgs) (envStream steps))
      (fun gs => LinearizableTrace kvModel
        (opEvents (kvProto (replicaAddrs cfgs)) (streamTrace gs)))

end deployment

end raft_kvnet
end EtcdGrove
end Perennial

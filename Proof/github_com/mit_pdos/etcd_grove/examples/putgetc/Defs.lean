/-
**`putgetc`** (M2, 2026-10-27, `notes/m2-plan.md`): putget's file, for putget with the
auto-compactor on (`common.StartCompactingServer`, revision mode, retention 1); putget's history
below is the original's.

**The adequacy example's `Main`: its named premises** (item 9, stage 2, 2026-10-18). Lean-first
(no Rocq counterpart).

`Main` (`examples/putgetc/putgetc.go`) is proved from `isPkgInit putgetc`, the right to listen on its
client address, the main thread's token, and the premises below
(`Spec/github_com/mit_pdos/etcd_grove/examples/putgetc/Main.lean`). Each is a premise of a callee's
spec that nothing in `Main`'s program can discharge: a statement about Go code the proofs do not
verify (names-only functions, the deployment), or a package fact that no initializer's theorem
gives yet. Which of them a closed adequacy theorem may take as a hypothesis (D19a) is
`notes/decisions.md`, D19r.

**The pure facts** (`BootFacts`): `bootstrap`'s result for this configuration, as Go computes it
(etcd's member id from the peer URLs and the cluster token, its 16 low bits not `0`, D19c; the
bootstrap log and the peers' contexts, one conf change adding the member, the node API's `BootLog`,
each of id `0` and one the server's `applyConfChange` takes).

**The Iris premises** (`premises`, persistent; since D19r was carried out, 2026-10-18, each a
triple of a function the program calls, D19a's second kind):
* `bootstrap`'s contract (`bootstrapContract`, D13b), at every server raft names of this one-member
  cluster (its peers `[id]`, static, the bootstrap log; at the storage registry they name; 2026-10-27,
  until then raft's names, with raft's no-snapshot and no-transfer modes and the policy `ccOk`), at
  the peers' contexts, for a configuration with the scalar fields `Main` sets (`cfgOk`) and its URLs
  (`urlsOk`), which the contract reads read-only (`bootCfgRO`), with the registry's authority;
* `proto.Marshal`'s contract at the bootstrap log's conf changes (`bootMarshal`; 2026-10-27, until
  then part of `bootstrap`'s contract's postcondition), which the cluster's allocation takes;
* the raft wrapper's trust-boundary contracts (`NodeStartSpec`'s): `rnLoggerZapOk`,
  `rnSetLoggerOk`, `rnTimeoutDetectorOk`, `rnNewStorageOk`, `rnTickerOk` at every raft
  environment whose tick resource is `True` (the server's, `srvEr`), `rnStopOkStarted` (`Stop` of
  a started node);
* `v3rpc.runsNoRequireLeader` (no client stream asks for a leader: a fact of the deployment).

What were package-fact premises until D19r was carried out are gone: `rnRaftStatusOk` and
`waitClosecInit` are now `etcdserver`'s and `pkg/wait`'s facts; `io.EOF` and `context`'s
`closedchan`, which came from the named Props `EofFromIoInit` and `ClosedchanFromContextInit`
until 2026-10-20, now come from `io`'s and `context`'s package facts (Perennial `init-facts`:
`v3rpc.eofVar_of_init`, `context.isClosedchanInit_of_init`).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.NewServer
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.InvWatch
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.InvStreamInterceptor
public import Proof.github_com.mit_pdos.etcd_grove.examples.putgetc.Base
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.InvGrpcStart
public import Proof.net.InvNet

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace putgetc

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section pure
variable [GooseExts]

/-- **`bootstrap`'s result, as Go computes it** (pure facts of the program): the member id `id`
(etcd's, computed by `bootstrap` from the configuration's peer URLs and cluster token:
`peerURL`, `putgetc`) with its 16 low bits not `0` (D19c), and the bootstrap log `bl` with the
peers' contexts `ctxs` (the node API's `BootLog`: one conf change adding the member, its context
`ctxs[0]`), each entry a conf change of id `0` that the server's `applyConfChange` takes
(`ccBootOk`). (2026-10-27, the server port: until then `srvBootLogOk (ccOk id) [id] bootLog`, under
the conf-change policy `ccOk id`, over raft's records.) -/
structure BootFacts (id : w64) (ctxs : List (List w8)) (bl : List Draft.LogEntry) : Prop where
  idLow : uint.Z id % 2 ^ 16 ≠ 0
  boot : Draft.BootLog [id] ctxs bl
  cc : ∀ e ∈ Draft.LogEntry.toEntries bl 0,
    ccIdOf e.Data' = W64 0 ∧ ccBootOk (GMap.listToSet [id]) e.Data'

/-- `Main`'s peer URL, `http://127.0.0.1:23801`. -/
def peerURL : _root_.Perennial.net.url.URL :=
  { (zero_val _root_.Perennial.net.url.URL) with Scheme' := go!"http", Host' := go!"127.0.0.1:23801" }

/-- `Main`'s client URL, `http://127.0.0.1:23791`. -/
def clientURL : _root_.Perennial.net.url.URL :=
  { (zero_val _root_.Perennial.net.url.URL) with Scheme' := go!"http", Host' := go!"127.0.0.1:23791" }

/-- **The URLs of `Main`'s configuration** (D19r (F)): the peer URLs `[peerURL]`, the client URLs
`[clientURL]`, the initial cluster's map `{putgetc ↦ [peerURL]}`. -/
def urlsOk (U : BootURLs) : Prop :=
  U.peer = [peerURL] ∧ U.client = [clientURL] ∧
    (∃ sl : GoSlice, U.initMap = GMap.insert go!"putgetc" sl ∅) ∧ U.initURLs go!"putgetc" = [peerURL]

/-- **The peer-URL directory of `Main`'s cluster** (D21 M2, 2026-10-19): its one member's peer
URL, `http://127.0.0.1:23801` (the members' records `bootstrap` makes name it), of the member `id`
only (`dirOne`; 2026-10-24, rafthttp stage 6d; until then every id's). -/
def putgetcDir (id : w64) : w64 → List GoString := dirOne id go!"http://127.0.0.1:23801"

end pure

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [v3rpc_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **The configuration `Main` passes to `NewServer`**, by its scalar fields (its pointers -- the
logger, the feature gate, the URLs, read through `bootCfgRO` -- are `Main`'s allocations): member
`putgetc` of a new cluster with token `putgetc`, data directory `putgetc.etcd`, raft's clock `100`
ms and `10` ticks. -/
def cfgOk (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) : Prop :=
  cfg.Name' = go!"putgetc" ∧ cfg.DataDir' = go!"putgetc.etcd" ∧
    cfg.InitialClusterToken' = go!"putgetc" ∧ cfg.NewCluster' = true ∧
    cfg.TickMs' = W64 100 ∧ cfg.ElectionTicks' = W64 10

/-- **`Main`'s named premises** (persistent; see the file header), at the bound `N` of the apply
thread's write tokens, the member id `id`, the peers' contexts `ctxs` and the bootstrap log `boot`: each a triple of a
function the program calls, whose postcondition holds fresh resources (D19a's second kind). -/
def premises (N : Nat) (id : w64) (ctxs : List (List w8)) (boot : List Draft.LogEntry) :
    IProp GF :=
  iprop(
    -- `bootstrap`'s contract (D13b), at every server raft names of the one-member cluster (2026-10-27,
    -- the server port: its peers `[id]`, static, the bootstrap log; at the storage registry they
    -- name), for `Main`'s configuration and URLs (D19r (B), (F)), at the peers' contexts `ctxs`
    (□ ∀ (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (U : BootURLs) (γ : SrvRaft),
      ⌜cfgOk cfg ∧ urlsOk U ∧ γ.vs = [id] ∧ γ.dyn = false ∧
        γ.boot = Draft.LogEntry.toEntries boot 0⌝ -∗
      letI : MemStorReg GF := ⟨γ.reg⟩; bootstrapContract cfg U γ id ctxs N (putgetcDir id)) ∗
    -- (2026-10-27, the server port) `proto.Marshal` of the peers' conf changes returns the bootstrap
    -- entries' bytes (raft's `bootMarshal`, which `StartNode` takes; the cluster's allocation's
    -- premise; until then `bootstrap`'s contract gave it)
    bootMarshal [id] ctxs (Draft.LogEntry.toEntries boot 0) ∗
    -- the raft wrapper's trust-boundary contracts (`NodeStartSpec`'s)
    rnLoggerZapOk ∗ rnSetLoggerOk ∗ rnTimeoutDetectorOk ∗ rnNewStorageOk ∗
    (□ ∀ E : RNEnv GF, ⌜E.T = iprop(True)⌝ -∗ rnTickerOk E) ∗
    rnStopOkStarted ∗
    -- the deployment: no client stream asks for a leader
    v3rpc.runsNoRequireLeader)

instance premises_persistent (N : Nat) (id : w64) (ctxs : List (List w8))
    (boot : List Draft.LogEntry) : Persistent (premises (GF := GF) N id ctxs boot) := by
  unfold premises; infer_instance

end defs

end putgetc
end EtcdGrove
end Perennial

/-
**The adequacy example's `Main`: its named premises** (item 9, stage 2, 2026-10-18). Lean-first
(no Rocq counterpart).

`Main` (`examples/putget/putget.go`) is proved from `isPkgInit putget`, the right to listen on its
client address, the main thread's token, and the premises below
(`Spec/github_com/mit_pdos/etcd_grove/examples/putget/Main.lean`). Each is a premise of a callee's
spec that nothing in `Main`'s program can discharge: a statement about Go code the proofs do not
verify (names-only functions, the deployment), or a package fact that no initializer's theorem
gives yet. Which of them a closed adequacy theorem may take as a hypothesis (D19a) is
`notes/decisions.md`, D19r.

**The pure facts** (`BootFacts`): `bootstrap`'s result for this configuration, as Go computes it
(etcd's member id from the peer URLs and the cluster token, its 16 low bits not `0`, D19c; the
bootstrap log, one conf change adding the member, id `0`, under the server's conf-change policy
`ccOk`).

**The Iris premises** (`premises`, persistent):
* `bootstrap`'s contract (`bootstrapContract`, D13b), at every raft names of this one-member
  cluster (configuration `{id}`, tracked `{id}`, the bootstrap log, the policy `ccOk`, static), for a
  configuration with the scalar fields `Main` sets (`cfgOk`);
* the raft wrapper's trust-boundary contracts (`NodeStartSpec`'s): `rnLoggerZapOk`,
  `rnSetLoggerOk`, `rnTimeoutDetectorOk`, `rnNewStorageOk`, `rnTickerOk` at every raft
  environment whose tick resource is `True` (the server's, `srvEr`), `∀ n, rnStopOk n`;
* the package facts no initializer theorem gives: `rnRaftStatusOk` (etcdserver's `raftStatusMu`
  over `raftStatus`), `waitClosecInit` (`pkg/wait`'s `closec`), `context.isClosedchanInit`
  (Perennial's `context`), `v3rpc.eofVar` (Perennial's `io.EOF`, D19j);
* `v3rpc.runsNoRequireLeader` (no client stream asks for a leader: a fact of the deployment).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.NewServer
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.InvWatch
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.InvStreamInterceptor
public import Proof.github_com.mit_pdos.etcd_grove.examples.putget.Base
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.InvGrpcStart
public import Proof.net.InvNet

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace putget

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section pure
variable [ext : FfiSyntax]

/-- **The server's conf-change policy for the one-member cluster `{id}`** (`srvCCPolicy`'s
clauses, D19c): a v1 conf change, a `ConfChange` encoding of id `0`, which changes nothing of the
configuration. -/
def ccOk (id : w64) : w32 → List w8 → Prop := fun ty d =>
  ty = W32 1 ∧ isConfChangeEncoding d ∧ ccIdOf d = W64 0 ∧ ccBootOk (GMap.listToSet [id]) d

/-- **`bootstrap`'s result, as Go computes it** (pure facts of the program): the member id `id`
(etcd's, from the peer URLs and the cluster token) with its 16 low bits not `0` (D19c), and the
bootstrap log `bootLog` (one conf change adding the member) under the policy `ccOk id`. -/
structure BootFacts (id : w64) (bootLog : List EntryM) : Prop where
  idLow : uint.Z id % 2 ^ 16 ≠ 0
  boot : BootLogOk (ccOk id) [id] bootLog

end pure

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [v3rpc_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [MemStorReg GF]

/-- **The configuration `Main` passes to `NewServer`**, by its scalar fields (its pointers -- the
logger, the feature gate, the URLs -- are `Main`'s allocations): member `putget` of a new
cluster with token `putget`, data directory `putget.etcd`, raft's clock `100` ms and `10` ticks. -/
def cfgOk (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) : Prop :=
  cfg.Name' = go!"putget" ∧ cfg.DataDir' = go!"putget.etcd" ∧
    cfg.InitialClusterToken' = go!"putget" ∧ cfg.NewCluster' = true ∧
    cfg.TickMs' = W64 100 ∧ cfg.ElectionTicks' = W64 10

/-- **`Main`'s named premises** (persistent; see the file header), at the bound `N` of the apply
thread's write tokens, the member id `id` and the bootstrap log `bootLog`. -/
def premises (N : Nat) (id : w64) (bootLog : List EntryM) : IProp GF :=
  iprop(
    -- `bootstrap`'s contract (D13b), at every raft names of the one-member cluster
    (□ ∀ (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (γ : RaftNames),
      ⌜cfgOk cfg ∧ γ.reCfg = GMap.listToSet [id] ∧ γ.reDyn = none ∧ γ.reCCOk = ccOk id ∧
        γ.reBoot = bootLog ∧ γ.reTracked = some (GMap.listToSet [id])⌝ -∗
      bootstrapContract cfg γ id bootLog N) ∗
    -- the raft wrapper's trust-boundary contracts (`NodeStartSpec`'s)
    rnLoggerZapOk ∗ rnSetLoggerOk ∗ rnTimeoutDetectorOk ∗ rnNewStorageOk ∗
    (□ ∀ E : RNEnv GF, ⌜E.T = iprop(True)⌝ -∗ rnTickerOk E) ∗
    (∀ n : Loc, rnStopOk n) ∗
    -- package facts no initializer theorem gives
    rnRaftStatusOk ∗ waitClosecInit ∗ context.isClosedchanInit ∗ v3rpc.eofVar ∗
    -- the deployment: no client stream asks for a leader
    v3rpc.runsNoRequireLeader)

instance premises_persistent (N : Nat) (id : w64) (bootLog : List EntryM) :
    Persistent (premises (GF := GF) N id bootLog) := by
  unfold premises; infer_instance

end defs

end putget
end EtcdGrove
end Perennial

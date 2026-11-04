/-
**A one-member example's start premises, shared** (2026-11-04, K4 of
`notes/k8s-compactor-plan.md`). Lean-first.

The one-member examples (`putget`, `compacted`, `compactwatch`, `lease`, `leasegrant`, `k8s/etcd3`)
each define the same two things, at their own configuration: `BootFacts`, `bootstrap`'s result for
the member as Go computes it, and `premises`, the named Iris premises of their `Main` (`bootstrap`'s
contract at the configuration, `proto.Marshal`'s at the bootstrap log, the raft wrapper's
trust-boundary contracts, the deployment's `runsNoRequireLeader`; `compactwatch/Defs.lean`'s
header says what each is). Here they are once, at the shared start's configuration of the member
`name` and its two addresses (`cfgOk name name`, `urls1`, `Defs.lean`; the directory `dir1`). The Kubernetes
compactor example is their first user; the older examples keep their copies for now (their
`Main.spec`s name them).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Defs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcdstart

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section pure
variable [GooseExts]

/-- **`bootstrap`'s result for a one-member cluster, as Go computes it** (pure facts of the
program): the member id `id` (etcd's, from the configuration's peer URLs and cluster token) with
its 16 low bits not `0` (D19c), and the bootstrap log `bl` with the peers' contexts `ctxs` (one conf
change adding the member), each entry a conf change of id `0` that the server's
`applyConfChange` takes. -/
structure BootFacts (id : w64) (ctxs : List (List w8)) (bl : List LogEntry) : Prop where
  idLow : uint.Z id % 2 ^ 16 ≠ 0
  boot : BootLog [id] ctxs bl
  cc : ∀ e ∈ LogEntry.toEntries bl 0,
    ccIdOf e.Data' = W64 0 ∧ ccBootOk (GMap.listToSet [id]) e.Data'

/-- **The peer-URL directory of a one-member cluster** (D21 M2; `dirOne`): the member `id`'s peer
URL `http://peer`. -/
def dir1 (peer : GoString) (id : w64) : w64 → List GoString := dirOne id (go!"http://" ++ peer)

end pure

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [v3rpc_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **A one-member `Main`'s named premises** (persistent; see the file header), for the member
`name` at the peer address `peer` and the client address `client` (the shared start's
configuration `cfgOk name name` and URLs `urls1`, the directory `dir1 peer`), at the bound `N` of
the apply thread's write tokens, the member id `id`, the peers' contexts `ctxs` and the bootstrap
log `boot`. -/
def premises (name peer client : GoString)
    (N : Nat) (id : w64) (ctxs : List (List w8)) (boot : List LogEntry) : IProp GF :=
  iprop(
    (□ ∀ (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (U : BootURLs) (γ : SrvRaft),
      ⌜cfgOk name name cfg ∧ urls1 name peer client U ∧ γ.vs = [id] ∧
        γ.rule = srvRule (W64 0) (LogEntry.toEntries boot 0) ∧
        γ.boot = LogEntry.toEntries boot 0⌝ -∗
      letI : MemStorReg GF := ⟨γ.reg⟩; bootstrapContract cfg U γ id ctxs N (dir1 peer id)) ∗
    bootMarshal [id] ctxs (LogEntry.toEntries boot 0) ∗
    rnLoggerZapOk ∗ rnSetLoggerOk ∗ rnTimeoutDetectorOk ∗ rnNewStorageOk ∗
    v3rpc.runsNoRequireLeader)

instance premises_persistent (name peer client : GoString) (N : Nat) (id : w64)
    (ctxs : List (List w8)) (boot : List LogEntry) :
    Persistent (premises (GF := GF) name peer client N id ctxs boot) := by
  unfold premises; infer_instance

end defs

end etcdstart
end EtcdGrove
end Perennial

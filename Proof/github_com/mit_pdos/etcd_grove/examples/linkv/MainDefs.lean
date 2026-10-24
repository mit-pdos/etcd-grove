/-
Lean-first (no Rocq counterpart).

# `Main`'s named premises (D20 (c), 2026-10-19)

`linkv`'s `Main` starts the one-member server as `examples/putget`'s does, on other ports and
names, so its premises are putget's (`Proof/.../putget/Defs.lean`, whose header explains each) at
`linkv`'s configuration: `cfgOk` (member and cluster token `linkv`, data directory `linkv.etcd`,
raft's clock), `urlsOk` (peer URL `http://127.0.0.1:23801`, client URL `http://127.0.0.1:23791`)
and the peer directory `linkvDir`. The pure facts (`putget.BootFacts`), the conf-change policy
(`putget.ccOk`) and the allocation (`putget.putget_alloc`) are putget's, which name no
configuration.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.putget.Defs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace linkv

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section pure
variable [ext : FfiSyntax]

/-- `Main`'s peer URL, `http://127.0.0.1:23801`. -/
def peerURL : _root_.Perennial.net.url.URL :=
  { (zero_val _root_.Perennial.net.url.URL) with Scheme' := go!"http", Host' := go!"127.0.0.1:23801" }

/-- `Main`'s client URL, `http://127.0.0.1:23791`. -/
def clientURL : _root_.Perennial.net.url.URL :=
  { (zero_val _root_.Perennial.net.url.URL) with Scheme' := go!"http", Host' := go!"127.0.0.1:23791" }

/-- **The URLs of `Main`'s configuration**: the peer URLs `[peerURL]`, the client URLs
`[clientURL]`, the initial cluster's map `{linkv ↦ [peerURL]}`. -/
def urlsOk (U : BootURLs) : Prop :=
  U.peer = [peerURL] ∧ U.client = [clientURL] ∧
    (∃ sl : GoSlice, U.initMap = GMap.insert go!"linkv" sl ∅) ∧ U.initURLs go!"linkv" = [peerURL]

/-- **The peer-URL directory of `Main`'s cluster**: its one member's peer URL, of the
member `id` only (`dirOne`; 2026-10-24, rafthttp stage 6d; until then every id's). -/
def linkvDir (id : w64) : w64 → List GoString := dirOne id go!"http://127.0.0.1:23801"

end pure

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [v3rpc_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **The configuration `Main` passes to `NewServer`**, by its scalar fields: member `linkv` of a
new cluster with token `linkv`, data directory `linkv.etcd`, raft's clock `100` ms and `10`
ticks. -/
def cfgOk (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) : Prop :=
  cfg.Name' = go!"linkv" ∧ cfg.DataDir' = go!"linkv.etcd" ∧
    cfg.InitialClusterToken' = go!"linkv" ∧ cfg.NewCluster' = true ∧
    cfg.TickMs' = W64 100 ∧ cfg.ElectionTicks' = W64 10

/-- **`Main`'s named premises** (persistent): putget's (`putget.premises`) at `linkv`'s
configuration, URLs and peer directory. -/
def premises (N : Nat) (id : w64) (bootLog : List EntryM) : IProp GF :=
  iprop(
    (□ ∀ (reg : GName) (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (U : BootURLs)
        (γ : RaftNames),
      ⌜cfgOk cfg ∧ urlsOk U ∧ γ.reCfg = GMap.listToSet [id] ∧ γ.reDyn = none ∧
        γ.reCCOk = putget.ccOk id ∧ γ.reBoot = bootLog ∧ γ.reNoSnap = true ∧ γ.reNoXfer = true⌝ -∗
      letI : MemStorReg GF := ⟨reg⟩; bootstrapContract cfg U γ id bootLog N (linkvDir id)) ∗
    rnLoggerZapOk ∗ rnSetLoggerOk ∗ rnTimeoutDetectorOk ∗ rnNewStorageOk ∗
    (□ ∀ E : RNEnv GF, ⌜E.T = iprop(True)⌝ -∗ rnTickerOk E) ∗
    rnStopOkStarted ∗
    v3rpc.runsNoRequireLeader)

instance premises_persistent (N : Nat) (id : w64) (bootLog : List EntryM) :
    Persistent (premises (GF := GF) N id bootLog) := by
  unfold premises; infer_instance

end defs

end linkv
end EtcdGrove
end Perennial

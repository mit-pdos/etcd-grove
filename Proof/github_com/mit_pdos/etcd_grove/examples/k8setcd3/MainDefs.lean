/-
Lean-first (no Rocq counterpart).

# k8setcd3: `Main`'s named premises (stage 6g)

`k8setcd3`'s `Main` starts the one-member server as `examples/linkvtxn`'s does (`common.StartServer`,
`common.Serve`), on other ports and names, so its premises are putget's (`Proof/.../putget/Defs.lean`, whose header explains each) at
`k8setcd3`'s configuration: `cfgOk` (member and cluster token `k8setcd3`, data directory `k8setcd3.etcd`,
raft's clock), `urlsOk` (peer URL `http://127.0.0.1:23906`, client URL `http://127.0.0.1:23896`)
and the peer directory `k8setcd3Dir`. The pure facts (`putget.BootFacts`), the conf-change policy
(`putget.ccOk`) are putget's and the allocation (`common.alloc1`) the shared start's, which name no
configuration.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.putget.Defs
public import Proof.go_etcd_io.etcd.client.v3.InvClientNewResult

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8setcd3

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section pure
variable [ext : FfiSyntax]

/-- `Main`'s peer URL, `http://127.0.0.1:23906`. -/
def peerURL : _root_.Perennial.net.url.URL :=
  { (zero_val _root_.Perennial.net.url.URL) with Scheme' := go!"http", Host' := go!"127.0.0.1:23906" }

/-- `Main`'s client URL, `http://127.0.0.1:23896`. -/
def clientURL : _root_.Perennial.net.url.URL :=
  { (zero_val _root_.Perennial.net.url.URL) with Scheme' := go!"http", Host' := go!"127.0.0.1:23896" }

/-- **The URLs of `Main`'s configuration**: the peer URLs `[peerURL]`, the client URLs
`[clientURL]`, the initial cluster's map `{k8setcd3 ↦ [peerURL]}`. -/
def urlsOk (U : BootURLs) : Prop :=
  U.peer = [peerURL] ∧ U.client = [clientURL] ∧
    (∃ sl : GoSlice, U.initMap = GMap.insert go!"k8setcd3" sl ∅) ∧ U.initURLs go!"k8setcd3" = [peerURL]

/-- **The peer-URL directory of `Main`'s cluster**: its one member's peer URL, of the
member `id` only (`dirOne`; 2026-10-24, rafthttp stage 6d; until then every id's). -/
def k8setcd3Dir (id : w64) : w64 → List GoString := dirOne id go!"http://127.0.0.1:23906"

end pure

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [v3rpc_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **The configuration `Main` passes to `NewServer`**, by its scalar fields: member `k8setcd3` of a
new cluster with token `k8setcd3`, data directory `k8setcd3.etcd`, raft's clock `100` ms and `10`
ticks. -/
def cfgOk (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) : Prop :=
  cfg.Name' = go!"k8setcd3" ∧ cfg.DataDir' = go!"k8setcd3.etcd" ∧
    cfg.InitialClusterToken' = go!"k8setcd3" ∧ cfg.NewCluster' = true ∧
    cfg.TickMs' = W64 100 ∧ cfg.ElectionTicks' = W64 10

/-- **`Main`'s named premises** (persistent): putget's (`putget.premises`) at `k8setcd3`'s
configuration, URLs and peer directory. -/
def premises (N : Nat) (id : w64) (bootLog : List EntryM) : IProp GF :=
  iprop(
    (□ ∀ (reg : GName) (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (U : BootURLs)
        (γ : RaftNames),
      ⌜cfgOk cfg ∧ urlsOk U ∧ γ.reCfg = GMap.listToSet [id] ∧ γ.reDyn = none ∧
        γ.reCCOk = putget.ccOk id ∧ γ.reBoot = bootLog ∧ γ.reNoSnap = true ∧ γ.reNoXfer = true⌝ -∗
      letI : MemStorReg GF := ⟨reg⟩; bootstrapContract cfg U γ id bootLog N (k8setcd3Dir id)) ∗
    rnLoggerZapOk ∗ rnSetLoggerOk ∗ rnTimeoutDetectorOk ∗ rnNewStorageOk ∗
    (□ ∀ E : RNEnv GF, ⌜E.T = iprop(True)⌝ -∗ rnTickerOk E) ∗
    rnStopOkStarted ∗
    v3rpc.runsNoRequireLeader)

omit package_sem in
/-- **The client's `ctx` field** (read-only; `etcd3.New` reads it through `c.Ctx()`): a marked
`sorry` until the client's `New` spec gives it ("From the etcd client proof", item 6 of
`notes/k8s-etcd3-plan.md`). -/
theorem client_ctx_field (cl : Loc) (eps : List GoString) (V : client.WEnv GF) :
    isNewClient cl eps V ⊢
      ∃ cx : GoInterface, structFieldRef go_etcd_io.etcd.client.v3.Client go!"ctx" cl ↦□ cx := by
  sorry

instance premises_persistent (N : Nat) (id : w64) (bootLog : List EntryM) :
    Persistent (premises (GF := GF) N id bootLog) := by
  unfold premises; infer_instance

end defs

end k8setcd3
end EtcdGrove
end Perennial

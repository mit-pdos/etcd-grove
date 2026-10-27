/-
**watchkv's vocabulary** (D23, 2026-10-20). Lean-first (no Rocq counterpart).

* The configuration `Main` starts its member with, as putget's (`Proof/.../putget/Defs.lean`,
  whose header explains each premise) at watchkv's names and ports: `cfgOk` (member and token
  `watchkv`, data directory `watchkv.etcd`), `urlsOk` (peer URL `http://127.0.0.1:23882`, client
  URL `http://127.0.0.1:23872`), the peer directory `wkDir`, and `premises`: putget's at these,
  (until 2026-10-20 also the transport premise `client.noRetryableStreamErr`, that the transport
  never fails a watch stream with a retryable code; gone with D25: the client watcher's
  reconnection is verified).
* The program's values: `genKeys`/`genVals` (`Gen`'s), `pairOf` (a `kv`'s key and value),
  `CheckOk` (what `check` needs not to panic).
* `revAt E r k v`: revision `r` of a sealed log of the server's store is the put of `k ↦ v` (no
  lease); two agree (`revAt_agree`: sealed logs are in prefix order).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.watchkv.Base
public import Proof.github_com.mit_pdos.etcd_grove.examples.common.WatchBase
public import Proof.github_com.mit_pdos.etcd_grove.examples.watchkv.Workload
public import Proof.github_com.mit_pdos.etcd_grove.examples.putget.Defs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace watchkv

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3
open github_com.mit_pdos.etcd_grove.examples.watchkv

section pure
variable [GooseExts]

/-- The program's structs (`kv`, `event`, `putRec`), by short names. -/
abbrev wkv := common.wkv
abbrev wev := common.wev
abbrev wrec := common.wrec

/-- `Main`'s peer URL, `http://127.0.0.1:23882`. -/
def peerURL : _root_.Perennial.net.url.URL :=
  { (zero_val _root_.Perennial.net.url.URL) with Scheme' := go!"http", Host' := go!"127.0.0.1:23882" }

/-- `Main`'s client URL, `http://127.0.0.1:23872`. -/
def clientURL : _root_.Perennial.net.url.URL :=
  { (zero_val _root_.Perennial.net.url.URL) with Scheme' := go!"http", Host' := go!"127.0.0.1:23872" }

/-- **The URLs of `Main`'s configuration**: the peer URLs `[peerURL]`, the client URLs
`[clientURL]`, the initial cluster's map `{watchkv ↦ [peerURL]}`. -/
def urlsOk (U : BootURLs) : Prop :=
  U.peer = [peerURL] ∧ U.client = [clientURL] ∧
    (∃ sl : GoSlice, U.initMap = GMap.insert go!"watchkv" sl ∅) ∧ U.initURLs go!"watchkv" = [peerURL]

/-- **The peer-URL directory of `Main`'s cluster**: its one member's peer URL, of the
member `id` only (`dirOne`; 2026-10-24, rafthttp stage 6d; until then every id's). -/
def wkDir (id : w64) : w64 → List GoString := dirOne id go!"http://127.0.0.1:23882"

/-- The prefix the writers' keys are under and the watch covers. -/
abbrev wkPfx : GoString := go!"wk/"

/-- The keys `Gen` picks from. -/
abbrev genKeys : List GoString := [go!"wk/k0", go!"wk/k1", go!"wk/k2"]

/- The values `Gen` picks from, a `KV`'s pair, a `KV` `Gen` may return, what `Check` needs not to
panic: the shared start's (`common/WatchBase.lean`). -/
export common (genVals pairOf GenKv CheckOk)

end pure

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [v3rpc_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **The configuration `Main` passes to `NewServer`**, by its scalar fields: member `watchkv` of
a new cluster with token `watchkv`, data directory `watchkv.etcd`, raft's clock `100` ms and `10`
ticks. -/
def cfgOk (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) : Prop :=
  cfg.Name' = go!"watchkv" ∧ cfg.DataDir' = go!"watchkv.etcd" ∧
    cfg.InitialClusterToken' = go!"watchkv" ∧ cfg.NewCluster' = true ∧
    cfg.TickMs' = W64 100 ∧ cfg.ElectionTicks' = W64 10

/-- **`Main`'s named premises** (persistent): putget's (`putget.premises`) at `watchkv`'s
configuration, URLs and peer directory. -/
def premises (N : Nat) (id : w64) (ctxs : List (List w8)) (boot : List Draft.LogEntry) :
    IProp GF :=
  iprop(
    (□ ∀ (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (U : BootURLs) (γ : SrvRaft),
      ⌜cfgOk cfg ∧ urlsOk U ∧ γ.vs = [id] ∧ γ.dyn = false ∧
        γ.boot = Draft.LogEntry.toEntries boot 0⌝ -∗
      letI : MemStorReg GF := ⟨γ.reg⟩; bootstrapContract cfg U γ id ctxs N (wkDir id)) ∗
    bootMarshal [id] ctxs (Draft.LogEntry.toEntries boot 0) ∗
    rnLoggerZapOk ∗ rnSetLoggerOk ∗ rnTimeoutDetectorOk ∗ rnNewStorageOk ∗
    (□ ∀ E : RNEnv GF, ⌜E.T = iprop(True)⌝ -∗ rnTickerOk E) ∗
    rnStopOkStarted ∗
    v3rpc.runsNoRequireLeader)

instance premises_persistent (N : Nat) (id : w64) (ctxs : List (List w8))
    (boot : List Draft.LogEntry) : Persistent (premises (GF := GF) N id ctxs boot) := by
  unfold premises; infer_instance

end defs

/- **Revision `r` of the store is the put of `k ↦ v`** (`common.revAt`, with its agreement). -/
export common (revAt revAt_persistent revAt_agree)


end watchkv
end EtcdGrove
end Perennial

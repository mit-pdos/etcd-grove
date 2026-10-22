/-
**cachekv's vocabulary** (2026-10-20). Lean-first (no Rocq counterpart).

watchkv's (`Proof/.../watchkv/Defs.lean`) at cachekv's names, ports and prefix:

* The configuration `Main` starts its member with, as putget's (`Proof/.../putget/Defs.lean`,
  whose header explains each premise) at cachekv's names and ports: `cfgOk` (member and token
  `cachekv`, data directory `cachekv.etcd`), `urlsOk` (peer URL `http://127.0.0.1:23861`, client
  URL `http://127.0.0.1:23851`), the peer directory `ckDir`, and `premises`: putget's at these
  (until 2026-10-20 also the transport premise `client.noRetryableStreamErr`, gone with D25: the
  client watcher's reconnection is verified).
* The program's values: `genKeys`/`genVals` (`Gen`'s, under the prefix `ck/`), `pairOf` (a `kv`'s
  key and value), `CheckOk` (what `check` needs not to panic).
* The workload (`watchkv.workload`), its logs (`watchkv.WkLog`) and `watchkv.revAt` are watchkv's.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.cachekv.Base
public import Proof.github_com.mit_pdos.etcd_grove.examples.watchkv.Defs
public import Proof.github_com.mit_pdos.etcd_grove.examples.common.WatchBase
public import Proof.github_com.mit_pdos.etcd_grove.examples.putget.Defs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cachekv

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3
open github_com.mit_pdos.etcd_grove.examples.cachekv

section pure
variable [ext : FfiSyntax]

/-- The program's structs (`kv`, `event`, `putRec`), by short names. -/
abbrev ckv := common.wkv
abbrev cev := common.wev
abbrev crec := common.wrec

/-- `Main`'s peer URL, `http://127.0.0.1:23861`. -/
def peerURL : _root_.Perennial.net.url.URL :=
  { (zero_val _root_.Perennial.net.url.URL) with Scheme' := go!"http", Host' := go!"127.0.0.1:23861" }

/-- `Main`'s client URL, `http://127.0.0.1:23851`. -/
def clientURL : _root_.Perennial.net.url.URL :=
  { (zero_val _root_.Perennial.net.url.URL) with Scheme' := go!"http", Host' := go!"127.0.0.1:23851" }

/-- **The URLs of `Main`'s configuration**: the peer URLs `[peerURL]`, the client URLs
`[clientURL]`, the initial cluster's map `{cachekv ↦ [peerURL]}`. -/
def urlsOk (U : BootURLs) : Prop :=
  U.peer = [peerURL] ∧ U.client = [clientURL] ∧
    (∃ sl : GoSlice, U.initMap = GMap.insert go!"cachekv" sl ∅) ∧ U.initURLs go!"cachekv" = [peerURL]

/-- **The peer-URL directory of `Main`'s cluster**: its one member's peer URL. -/
def ckDir (_ : w64) : List GoString := [go!"http://127.0.0.1:23861"]

/-- The prefix the writers' keys are under and the watch covers. -/
abbrev ckPfx : GoString := go!"ck/"

/-- The keys `Gen` picks from. -/
abbrev genKeys : List GoString := [go!"ck/k0", go!"ck/k1", go!"ck/k2"]

/- The values `Gen` picks from, a `KV`'s pair, a `KV` `Gen` may return, what `Check` needs not to
panic: the shared start's (`common/WatchBase.lean`). -/
export common (genVals pairOf GenKv CheckOk)

end pure

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [v3rpc_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **The configuration `Main` passes to `NewServer`**, by its scalar fields: member `cachekv` of
a new cluster with token `cachekv`, data directory `cachekv.etcd`, raft's clock `100` ms and `10`
ticks. -/
def cfgOk (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) : Prop :=
  cfg.Name' = go!"cachekv" ∧ cfg.DataDir' = go!"cachekv.etcd" ∧
    cfg.InitialClusterToken' = go!"cachekv" ∧ cfg.NewCluster' = true ∧
    cfg.TickMs' = W64 100 ∧ cfg.ElectionTicks' = W64 10

/-- **`Main`'s named premises** (persistent): putget's (`putget.premises`) at `cachekv`'s
configuration, URLs and peer directory. -/
def premises (N : Nat) (id : w64) (bootLog : List EntryM) : IProp GF :=
  iprop(
    (□ ∀ (reg : GName) (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (U : BootURLs)
        (γ : RaftNames),
      ⌜cfgOk cfg ∧ urlsOk U ∧ γ.reCfg = GMap.listToSet [id] ∧ γ.reDyn = none ∧
        γ.reCCOk = putget.ccOk id ∧ γ.reBoot = bootLog ∧ γ.reNoSnap = true ∧ γ.reNoXfer = true⌝ -∗
      letI : MemStorReg GF := ⟨reg⟩; bootstrapContract cfg U γ id bootLog N ckDir) ∗
    rnLoggerZapOk ∗ rnSetLoggerOk ∗ rnTimeoutDetectorOk ∗ rnNewStorageOk ∗
    (□ ∀ E : RNEnv GF, ⌜E.T = iprop(True)⌝ -∗ rnTickerOk E) ∗
    rnStopOkStarted ∗
    v3rpc.runsNoRequireLeader)

instance premises_persistent (N : Nat) (id : w64) (bootLog : List EntryM) :
    Persistent (premises (GF := GF) N id bootLog) := by
  unfold premises; infer_instance

end defs

end cachekv
end EtcdGrove
end Perennial
